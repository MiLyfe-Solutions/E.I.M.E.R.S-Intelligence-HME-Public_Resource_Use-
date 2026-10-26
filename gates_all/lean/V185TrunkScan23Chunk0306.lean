import V185TrunkScan23Chunk0305

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1810425 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_1810425 : Nat := 118140960795 + 1810425 * 2 ^ 59
def prefixEnd_1810425 : Nat := 4983230072969 + 3 ^ 40 * 1810425 * 2
def baseEnd_1810425 : Nat := 309872737972061479187171

theorem tailTrace_1810425 : CollatzResearch.WordTrace tailWord_1810425 prefixEnd_1810425 309872737972061479187171 := by
  unfold tailWord_1810425
  simp only [CollatzResearch.WordTrace]
  refine ⟨66031624466146895818760729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44021082977431263879173819 66031624466146895818760729)
  ·
    refine ⟨49523718349610171864070547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66031624466146895818760729 49523718349610171864070547)
    ·
      refine ⟨74285577524415257796105821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49523718349610171864070547 74285577524415257796105821)
      ·
        refine ⟨27857091571655721673539683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74285577524415257796105821 27857091571655721673539683)
        ·
          refine ⟨41785637357483582510309525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857091571655721673539683 41785637357483582510309525)
          ·
            refine ⟨1958701751132042930170759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41785637357483582510309525 1958701751132042930170759)
            ·
              refine ⟨2938052626698064395256139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958701751132042930170759 2938052626698064395256139)
              ·
                refine ⟨4407078940047096592884209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938052626698064395256139 4407078940047096592884209)
                ·
                  refine ⟨3305309205035322444663157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407078940047096592884209 3305309205035322444663157)
                  ·
                    refine ⟨309872737972061479187171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3305309205035322444663157 309872737972061479187171)
                    ·
                      rfl

theorem cell23_1810425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_1810425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810425 prefixEnd_1810425 := by exact prefixLift 1810425
  have htrace : WordTrace (prefixWord ++ tailWord_1810425) baseStart_1810425 baseEnd_1810425 := by
    simpa [prefixWord, tailWord_1810425, baseEnd_1810425] using wordTrace_append hprefix tailTrace_1810425
  have hstable : (prefixWord ++ tailWord_1810425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810425).length < 2 ^ (prefixWord ++ tailWord_1810425).sum := by decide
  have hdescent : baseEnd_1810425 < baseStart_1810425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810428 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1810428 : Nat := 118140960795 + 1810428 * 2 ^ 59
def prefixEnd_1810428 : Nat := 4983230072969 + 3 ^ 40 * 1810428 * 2
def baseEnd_1810428 : Nat := 929619754358147925823999

theorem tailTrace_1810428 : CollatzResearch.WordTrace tailWord_1810428 prefixEnd_1810428 929619754358147925823999 := by
  unfold tailWord_1810428
  simp only [CollatzResearch.WordTrace]
  refine ⟨33015866942568013665559969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44021155923424018220746625 33015866942568013665559969)
  ·
    refine ⟨24761900206926010249169977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33015866942568013665559969 24761900206926010249169977)
    ·
      refine ⟨18571425155194507686877483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24761900206926010249169977 18571425155194507686877483)
      ·
        refine ⟨27857137732791761530316225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18571425155194507686877483 27857137732791761530316225)
        ·
          refine ⟨20892853299593821147737169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27857137732791761530316225 20892853299593821147737169)
          ·
            refine ⟨15669639974695365860802877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20892853299593821147737169 15669639974695365860802877)
            ·
              refine ⟨5876114990510762197801079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15669639974695365860802877 5876114990510762197801079)
              ·
                refine ⟨8814172485766143296701619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876114990510762197801079 8814172485766143296701619)
                ·
                  refine ⟨13221258728649214945052429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8814172485766143296701619 13221258728649214945052429)
                  ·
                    refine ⟨4957972023243455604394661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13221258728649214945052429 4957972023243455604394661)
                    ·
                      refine ⟨929619754358147925823999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4957972023243455604394661 929619754358147925823999)
                      ·
                        rfl

theorem cell23_1810428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1810428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810428 prefixEnd_1810428 := by exact prefixLift 1810428
  have htrace : WordTrace (prefixWord ++ tailWord_1810428) baseStart_1810428 baseEnd_1810428 := by
    simpa [prefixWord, tailWord_1810428, baseEnd_1810428] using wordTrace_append hprefix tailTrace_1810428
  have hstable : (prefixWord ++ tailWord_1810428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810428).length < 2 ^ (prefixWord ++ tailWord_1810428).sum := by decide
  have hdescent : baseEnd_1810428 < baseStart_1810428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810495 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 3]
def baseStart_1810495 : Nat := 118140960795 + 1810495 * 2 ^ 59
def prefixEnd_1810495 : Nat := 4983230072969 + 3 ^ 40 * 1810495 * 2
def baseEnd_1810495 : Nat := 929654157561999163686191

theorem tailTrace_1810495 : CollatzResearch.WordTrace tailWord_1810495 prefixEnd_1810495 929654157561999163686191 := by
  unfold tailWord_1810495
  simp only [CollatzResearch.WordTrace]
  refine ⟨66034177575893297773808939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44022785050595531849205959 66034177575893297773808939)
  ·
    refine ⟨99051266363839946660713409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66034177575893297773808939 99051266363839946660713409)
    ·
      refine ⟨74288449772879959995535057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99051266363839946660713409 74288449772879959995535057)
      ·
        refine ⟨55716337329659969996651293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74288449772879959995535057 55716337329659969996651293)
        ·
          refine ⟨20893626498622488748744235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55716337329659969996651293 20893626498622488748744235)
          ·
            refine ⟨31340439747933733123116353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20893626498622488748744235 31340439747933733123116353)
            ·
              refine ⟨23505329810950299842337265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31340439747933733123116353 23505329810950299842337265)
              ·
                refine ⟨17628997358212724881752949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23505329810950299842337265 17628997358212724881752949)
                ·
                  refine ⟨1652718502332442957664339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17628997358212724881752949 1652718502332442957664339)
                  ·
                    refine ⟨2479077753498664436496509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1652718502332442957664339 2479077753498664436496509)
                    ·
                      refine ⟨929654157561999163686191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479077753498664436496509 929654157561999163686191)
                      ·
                        rfl

theorem cell23_1810495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_1810495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810495 prefixEnd_1810495 := by exact prefixLift 1810495
  have htrace : WordTrace (prefixWord ++ tailWord_1810495) baseStart_1810495 baseEnd_1810495 := by
    simpa [prefixWord, tailWord_1810495, baseEnd_1810495] using wordTrace_append hprefix tailTrace_1810495
  have hstable : (prefixWord ++ tailWord_1810495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810495).length < 2 ^ (prefixWord ++ tailWord_1810495).sum := by decide
  have hdescent : baseEnd_1810495 < baseStart_1810495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810502 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1810502 : Nat := 118140960795 + 1810502 * 2 ^ 59
def prefixEnd_1810502 : Nat := 4983230072969 + 3 ^ 40 * 1810502 * 2
def baseEnd_1810502 : Nat := 103295305769620070699851

theorem tailTrace_1810502 : CollatzResearch.WordTrace tailWord_1810502 prefixEnd_1810502 103295305769620070699851 := by
  unfold tailWord_1810502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063576027714623061541055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44022955257911958646209173 2063576027714623061541055)
  ·
    refine ⟨3095364041571934592311583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063576027714623061541055 3095364041571934592311583)
    ·
      refine ⟨4643046062357901888467375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095364041571934592311583 4643046062357901888467375)
      ·
        refine ⟨6964569093536852832701063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643046062357901888467375 6964569093536852832701063)
        ·
          refine ⟨10446853640305279249051595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964569093536852832701063 10446853640305279249051595)
          ·
            refine ⟨15670280460457918873577393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446853640305279249051595 15670280460457918873577393)
            ·
              refine ⟨11752710345343439155183045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15670280460457918873577393 11752710345343439155183045)
              ·
                refine ⟨2203633189751894841596821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11752710345343439155183045 2203633189751894841596821)
                ·
                  refine ⟨103295305769620070699851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2203633189751894841596821 103295305769620070699851)
                  ·
                    rfl

theorem cell23_1810502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1810502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810502 prefixEnd_1810502 := by exact prefixLift 1810502
  have htrace : WordTrace (prefixWord ++ tailWord_1810502) baseStart_1810502 baseEnd_1810502 := by
    simpa [prefixWord, tailWord_1810502, baseEnd_1810502] using wordTrace_append hprefix tailTrace_1810502
  have hstable : (prefixWord ++ tailWord_1810502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810502).length < 2 ^ (prefixWord ++ tailWord_1810502).sum := by decide
  have hdescent : baseEnd_1810502 < baseStart_1810502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810535 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1810535 : Nat := 118140960795 + 1810535 * 2 ^ 59
def prefixEnd_1810535 : Nat := 4983230072969 + 3 ^ 40 * 1810535 * 2
def baseEnd_1810535 : Nat := 929674696788179007186007

theorem tailTrace_1810535 : CollatzResearch.WordTrace tailWord_1810535 prefixEnd_1810535 929674696788179007186007 := by
  unfold tailWord_1810535
  simp only [CollatzResearch.WordTrace]
  refine ⟨66035636495748384605265059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44023757663832256403510039 66035636495748384605265059)
  ·
    refine ⟨99053454743622576907897589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66035636495748384605265059 99053454743622576907897589)
    ·
      refine ⟨9286261382214616585115399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99053454743622576907897589 9286261382214616585115399)
      ·
        refine ⟨13929392073321924877673099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286261382214616585115399 13929392073321924877673099)
        ·
          refine ⟨20894088109982887316509649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13929392073321924877673099 20894088109982887316509649)
          ·
            refine ⟨15670566082487165487382237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20894088109982887316509649 15670566082487165487382237)
            ·
              refine ⟨5876462280932687057768339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15670566082487165487382237 5876462280932687057768339)
              ·
                refine ⟨8814693421399030586652509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876462280932687057768339 8814693421399030586652509)
                ·
                  refine ⟨3305510033024636469994691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8814693421399030586652509 3305510033024636469994691)
                  ·
                    refine ⟨4958265049536954704992037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3305510033024636469994691 4958265049536954704992037)
                    ·
                      refine ⟨929674696788179007186007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4958265049536954704992037 929674696788179007186007)
                      ·
                        rfl

theorem cell23_1810535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1810535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810535 prefixEnd_1810535 := by exact prefixLift 1810535
  have htrace : WordTrace (prefixWord ++ tailWord_1810535) baseStart_1810535 baseEnd_1810535 := by
    simpa [prefixWord, tailWord_1810535, baseEnd_1810535] using wordTrace_append hprefix tailTrace_1810535
  have hstable : (prefixWord ++ tailWord_1810535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810535).length < 2 ^ (prefixWord ++ tailWord_1810535).sum := by decide
  have hdescent : baseEnd_1810535 < baseStart_1810535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810586 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1810586 : Nat := 118140960795 + 1810586 * 2 ^ 59
def prefixEnd_1810586 : Nat := 4983230072969 + 3 ^ 40 * 1810586 * 2
def baseEnd_1810586 : Nat := 929700884301558307648273

theorem tailTrace_1810586 : CollatzResearch.WordTrace tailWord_1810586 prefixEnd_1810586 929700884301558307648273 := by
  unfold tailWord_1810586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16509374154640905078842903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44024997745709080210247741 16509374154640905078842903)
  ·
    refine ⟨24764061231961357618264355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16509374154640905078842903 24764061231961357618264355)
    ·
      refine ⟨37146091847942036427396533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24764061231961357618264355 37146091847942036427396533)
      ·
        refine ⟨3482446110744565915068425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37146091847942036427396533 3482446110744565915068425)
        ·
          refine ⟨2611834583058424436301319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482446110744565915068425 2611834583058424436301319)
          ·
            refine ⟨3917751874587636654451979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611834583058424436301319 3917751874587636654451979)
            ·
              refine ⟨5876627811881454981677969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917751874587636654451979 5876627811881454981677969)
              ·
                refine ⟨4407470858911091236258477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876627811881454981677969 4407470858911091236258477)
                ·
                  refine ⟨1652801572091659213596929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4407470858911091236258477 1652801572091659213596929)
                  ·
                    refine ⟨1239601179068744410197697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652801572091659213596929 1239601179068744410197697)
                    ·
                      refine ⟨929700884301558307648273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239601179068744410197697 929700884301558307648273)
                      ·
                        rfl

theorem cell23_1810586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1810586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810586 prefixEnd_1810586 := by exact prefixLift 1810586
  have htrace : WordTrace (prefixWord ++ tailWord_1810586) baseStart_1810586 baseEnd_1810586 := by
    simpa [prefixWord, tailWord_1810586, baseEnd_1810586] using wordTrace_append hprefix tailTrace_1810586
  have hstable : (prefixWord ++ tailWord_1810586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810586).length < 2 ^ (prefixWord ++ tailWord_1810586).sum := by decide
  have hdescent : baseEnd_1810586 < baseStart_1810586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810613 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1810613 : Nat := 118140960795 + 1810613 * 2 ^ 59
def prefixEnd_1810613 : Nat := 4983230072969 + 3 ^ 40 * 1810613 * 2
def baseEnd_1810613 : Nat := 309904916093076567336883

theorem tailTrace_1810613 : CollatzResearch.WordTrace tailWord_1810613 prefixEnd_1810613 309904916093076567336883 := by
  unfold tailWord_1810613
  simp only [CollatzResearch.WordTrace]
  refine ⟨66038481389465803926604493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44025654259643869284402995 66038481389465803926604493)
  ·
    refine ⟨24764430521049676472476685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66038481389465803926604493 24764430521049676472476685)
    ·
      refine ⟨9286661445393628677178757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24764430521049676472476685 9286661445393628677178757)
      ·
        refine ⟨1741249021011305376971017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9286661445393628677178757 1741249021011305376971017)
        ·
          refine ⟨1305936765758479032728263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741249021011305376971017 1305936765758479032728263)
          ·
            refine ⟨1958905148637718549092395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305936765758479032728263 1958905148637718549092395)
            ·
              refine ⟨2938357722956577823638593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958905148637718549092395 2938357722956577823638593)
              ·
                refine ⟨2203768292217433367728945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938357722956577823638593 2203768292217433367728945)
                ·
                  refine ⟨1652826219163075025796709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2203768292217433367728945 1652826219163075025796709)
                  ·
                    refine ⟨309904916093076567336883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652826219163075025796709 309904916093076567336883)
                    ·
                      rfl

theorem cell23_1810613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1810613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810613 prefixEnd_1810613 := by exact prefixLift 1810613
  have htrace : WordTrace (prefixWord ++ tailWord_1810613) baseStart_1810613 baseEnd_1810613 := by
    simpa [prefixWord, tailWord_1810613, baseEnd_1810613] using wordTrace_append hprefix tailTrace_1810613
  have hstable : (prefixWord ++ tailWord_1810613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810613).length < 2 ^ (prefixWord ++ tailWord_1810613).sum := by decide
  have hdescent : baseEnd_1810613 < baseStart_1810613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810636 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1810636 : Nat := 118140960795 + 1810636 * 2 ^ 59
def prefixEnd_1810636 : Nat := 4983230072969 + 3 ^ 40 * 1810636 * 2
def baseEnd_1810636 : Nat := 929726558334283112023043

theorem tailTrace_1810636 : CollatzResearch.WordTrace tailWord_1810636 prefixEnd_1810636 929726558334283112023043 := by
  unfold tailWord_1810636
  simp only [CollatzResearch.WordTrace]
  refine ⟨33019660134191239427345881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44026213512254985903127841 33019660134191239427345881)
  ·
    refine ⟨24764745100643429570509411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33019660134191239427345881 24764745100643429570509411)
    ·
      refine ⟨37147117650965144355764117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24764745100643429570509411 37147117650965144355764117)
      ·
        refine ⟨1741271139888991141676443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37147117650965144355764117 1741271139888991141676443)
        ·
          refine ⟨2611906709833486712514665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741271139888991141676443 2611906709833486712514665)
          ·
            refine ⟨1958930032375115034385999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611906709833486712514665 1958930032375115034385999)
            ·
              refine ⟨2938395048562672551578999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958930032375115034385999 2938395048562672551578999)
              ·
                refine ⟨4407592572844008827368499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938395048562672551578999 4407592572844008827368499)
                ·
                  refine ⟨6611388859266013241052749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407592572844008827368499 6611388859266013241052749)
                  ·
                    refine ⟨2479270822224754965394781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6611388859266013241052749 2479270822224754965394781)
                    ·
                      refine ⟨929726558334283112023043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479270822224754965394781 929726558334283112023043)
                      ·
                        rfl

theorem cell23_1810636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1810636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810636 prefixEnd_1810636 := by exact prefixLift 1810636
  have htrace : WordTrace (prefixWord ++ tailWord_1810636) baseStart_1810636 baseEnd_1810636 := by
    simpa [prefixWord, tailWord_1810636, baseEnd_1810636] using wordTrace_append hprefix tailTrace_1810636
  have hstable : (prefixWord ++ tailWord_1810636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810636).length < 2 ^ (prefixWord ++ tailWord_1810636).sum := by decide
  have hdescent : baseEnd_1810636 < baseStart_1810636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810682 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_1810682 : Nat := 118140960795 + 1810682 * 2 ^ 59
def prefixEnd_1810682 : Nat := 4983230072969 + 3 ^ 40 * 1810682 * 2
def baseEnd_1810682 : Nat := 103305575382709992449759

theorem tailTrace_1810682 : CollatzResearch.WordTrace tailWord_1810682 prefixEnd_1810682 103305575382709992449759 := by
  unfold tailWord_1810682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510249506553957177716575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44027332017477219140577533 16510249506553957177716575)
  ·
    refine ⟨24765374259830935766574863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16510249506553957177716575 24765374259830935766574863)
    ·
      refine ⟨37148061389746403649862295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765374259830935766574863 37148061389746403649862295)
      ·
        refine ⟨55722092084619605474793443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37148061389746403649862295 55722092084619605474793443)
        ·
          refine ⟨83583138126929408212190165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55722092084619605474793443 83583138126929408212190165)
          ·
            refine ⟨1958979799849908004973207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83583138126929408212190165 1958979799849908004973207)
            ·
              refine ⟨2938469699774862007459811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958979799849908004973207 2938469699774862007459811)
              ·
                refine ⟨4407704549662293011189717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938469699774862007459811 4407704549662293011189717)
                ·
                  refine ⟨103305575382709992449759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4407704549662293011189717 103305575382709992449759)
                  ·
                    rfl

theorem cell23_1810682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_1810682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810682 prefixEnd_1810682 := by exact prefixLift 1810682
  have htrace : WordTrace (prefixWord ++ tailWord_1810682) baseStart_1810682 baseEnd_1810682 := by
    simpa [prefixWord, tailWord_1810682, baseEnd_1810682] using wordTrace_append hprefix tailTrace_1810682
  have hstable : (prefixWord ++ tailWord_1810682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810682).length < 2 ^ (prefixWord ++ tailWord_1810682).sum := by decide
  have hdescent : baseEnd_1810682 < baseStart_1810682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810712 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_1810712 : Nat := 118140960795 + 1810712 * 2 ^ 59
def prefixEnd_1810712 : Nat := 4983230072969 + 3 ^ 40 * 1810712 * 2
def baseEnd_1810712 : Nat := 309921860954674938224231

theorem tailTrace_1810712 : CollatzResearch.WordTrace tailWord_1810712 prefixEnd_1810712 309921860954674938224231 := by
  unfold tailWord_1810712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33021046108053571917229195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44028061477404762556305593 33021046108053571917229195)
  ·
    refine ⟨49531569162080357875843793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33021046108053571917229195 49531569162080357875843793)
    ·
      refine ⟨37148676871560268406882845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49531569162080357875843793 37148676871560268406882845)
      ·
        refine ⟨13930753826835100652581067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37148676871560268406882845 13930753826835100652581067)
        ·
          refine ⟨20896130740252650978871601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13930753826835100652581067 20896130740252650978871601)
          ·
            refine ⟨15672098055189488234153701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20896130740252650978871601 15672098055189488234153701)
            ·
              refine ⟨2938518385348029043903819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15672098055189488234153701 2938518385348029043903819)
              ·
                refine ⟨4407777578022043565855729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938518385348029043903819 4407777578022043565855729)
                ·
                  refine ⟨3305833183516532674391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407777578022043565855729 3305833183516532674391797)
                  ·
                    refine ⟨309921860954674938224231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3305833183516532674391797 309921860954674938224231)
                    ·
                      rfl

theorem cell23_1810712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_1810712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810712 prefixEnd_1810712 := by exact prefixLift 1810712
  have htrace : WordTrace (prefixWord ++ tailWord_1810712) baseStart_1810712 baseEnd_1810712 := by
    simpa [prefixWord, tailWord_1810712, baseEnd_1810712] using wordTrace_append hprefix tailTrace_1810712
  have hstable : (prefixWord ++ tailWord_1810712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810712).length < 2 ^ (prefixWord ++ tailWord_1810712).sum := by decide
  have hdescent : baseEnd_1810712 < baseStart_1810712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810715 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_1810715 : Nat := 118140960795 + 1810715 * 2 ^ 59
def prefixEnd_1810715 : Nat := 4983230072969 + 3 ^ 40 * 1810715 * 2
def baseEnd_1810715 : Nat := 929767123305988302935179

theorem tailTrace_1810715 : CollatzResearch.WordTrace tailWord_1810715 prefixEnd_1810715 929767123305988302935179 := by
  unfold tailWord_1810715
  simp only [CollatzResearch.WordTrace]
  refine ⟨66042201635096275346817599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44028134423397516897878399 66042201635096275346817599)
  ·
    refine ⟨99063302452644413020226399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66042201635096275346817599 99063302452644413020226399)
    ·
      refine ⟨148594953678966619530339599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99063302452644413020226399 148594953678966619530339599)
      ·
        refine ⟨222892430518449929295509399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148594953678966619530339599 222892430518449929295509399)
        ·
          refine ⟨334338645777674893943264099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222892430518449929295509399 334338645777674893943264099)
          ·
            refine ⟨501507968666512340914896149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334338645777674893943264099 501507968666512340914896149)
            ·
              refine ⟨23508186031242765980385757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 501507968666512340914896149 23508186031242765980385757)
              ·
                refine ⟨8815569761716037242644659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23508186031242765980385757 8815569761716037242644659)
                ·
                  refine ⟨13223354642574055863966989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815569761716037242644659 13223354642574055863966989)
                  ·
                    refine ⟨4958757990965270948987621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13223354642574055863966989 4958757990965270948987621)
                    ·
                      refine ⟨929767123305988302935179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4958757990965270948987621 929767123305988302935179)
                      ·
                        rfl

theorem cell23_1810715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_1810715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810715 prefixEnd_1810715 := by exact prefixLift 1810715
  have htrace : WordTrace (prefixWord ++ tailWord_1810715) baseStart_1810715 baseEnd_1810715 := by
    simpa [prefixWord, tailWord_1810715, baseEnd_1810715] using wordTrace_append hprefix tailTrace_1810715
  have hstable : (prefixWord ++ tailWord_1810715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810715).length < 2 ^ (prefixWord ++ tailWord_1810715).sum := by decide
  have hdescent : baseEnd_1810715 < baseStart_1810715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810722 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1810722 : Nat := 118140960795 + 1810722 * 2 ^ 59
def prefixEnd_1810722 : Nat := 4983230072969 + 3 ^ 40 * 1810722 * 2
def baseEnd_1810722 : Nat := 929770717670569775547647

theorem tailTrace_1810722 : CollatzResearch.WordTrace tailWord_1810722 prefixEnd_1810722 929770717670569775547647 := by
  unfold tailWord_1810722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510614236517728885580605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44028304630713943694881613 16510614236517728885580605)
  ·
    refine ⟨6191480338694148332092727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16510614236517728885580605 6191480338694148332092727)
    ·
      refine ⟨9287220508041222498139091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191480338694148332092727 9287220508041222498139091)
      ·
        refine ⟨13930830762061833747208637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9287220508041222498139091 13930830762061833747208637)
        ·
          refine ⟨5224061535773187655203239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13930830762061833747208637 5224061535773187655203239)
          ·
            refine ⟨7836092303659781482804859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224061535773187655203239 7836092303659781482804859)
            ·
              refine ⟨11754138455489672224207289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836092303659781482804859 11754138455489672224207289)
              ·
                refine ⟨8815603841617254168155467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754138455489672224207289 8815603841617254168155467)
                ·
                  refine ⟨13223405762425881252233201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815603841617254168155467 13223405762425881252233201)
                  ·
                    refine ⟨9917554321819410939174901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13223405762425881252233201 9917554321819410939174901)
                    ·
                      refine ⟨929770717670569775547647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9917554321819410939174901 929770717670569775547647)
                      ·
                        rfl

theorem cell23_1810722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1810722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810722 prefixEnd_1810722 := by exact prefixLift 1810722
  have htrace : WordTrace (prefixWord ++ tailWord_1810722) baseStart_1810722 baseEnd_1810722 := by
    simpa [prefixWord, tailWord_1810722, baseEnd_1810722] using wordTrace_append hprefix tailTrace_1810722
  have hstable : (prefixWord ++ tailWord_1810722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810722).length < 2 ^ (prefixWord ++ tailWord_1810722).sum := by decide
  have hdescent : baseEnd_1810722 < baseStart_1810722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810727 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1810727 : Nat := 118140960795 + 1810727 * 2 ^ 59
def prefixEnd_1810727 : Nat := 4983230072969 + 3 ^ 40 * 1810727 * 2
def baseEnd_1810727 : Nat := 929773285073842255985125

theorem tailTrace_1810727 : CollatzResearch.WordTrace tailWord_1810727 prefixEnd_1810727 929773285073842255985125 := by
  unfold tailWord_1810727
  simp only [CollatzResearch.WordTrace]
  refine ⟨66042639311052801396254435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44028426207368534264169623 66042639311052801396254435)
  ·
    refine ⟨99063958966579202094381653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66042639311052801396254435 99063958966579202094381653)
    ·
      refine ⟨1160905769139600024543535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 99063958966579202094381653 1160905769139600024543535)
      ·
        refine ⟨1741358653709400036815303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160905769139600024543535 1741358653709400036815303)
        ·
          refine ⟨2612037980564100055222955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741358653709400036815303 2612037980564100055222955)
          ·
            refine ⟨3918056970846150082834433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612037980564100055222955 3918056970846150082834433)
            ·
              refine ⟨2938542728134612562125825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918056970846150082834433 2938542728134612562125825)
              ·
                refine ⟨2203907046100959421594369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938542728134612562125825 2203907046100959421594369)
                ·
                  refine ⟨1652930284575719566195777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2203907046100959421594369 1652930284575719566195777)
                  ·
                    refine ⟨1239697713431789674646833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1652930284575719566195777 1239697713431789674646833)
                    ·
                      refine ⟨929773285073842255985125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239697713431789674646833 929773285073842255985125)
                      ·
                        rfl

theorem cell23_1810727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1810727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810727 prefixEnd_1810727 := by exact prefixLift 1810727
  have htrace : WordTrace (prefixWord ++ tailWord_1810727) baseStart_1810727 baseEnd_1810727 := by
    simpa [prefixWord, tailWord_1810727, baseEnd_1810727] using wordTrace_append hprefix tailTrace_1810727
  have hstable : (prefixWord ++ tailWord_1810727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810727).length < 2 ^ (prefixWord ++ tailWord_1810727).sum := by decide
  have hdescent : baseEnd_1810727 < baseStart_1810727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810732 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_1810732 : Nat := 118140960795 + 1810732 * 2 ^ 59
def prefixEnd_1810732 : Nat := 4983230072969 + 3 ^ 40 * 1810732 * 2
def baseEnd_1810732 : Nat := 929775852477114736422601

theorem tailTrace_1810732 : CollatzResearch.WordTrace tailWord_1810732 prefixEnd_1810732 929775852477114736422601 := by
  unfold tailWord_1810732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33021410838017343625093225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44028547784023124833457633 33021410838017343625093225)
  ·
    refine ⟨24766058128513007718819919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33021410838017343625093225 24766058128513007718819919)
    ·
      refine ⟨37149087192769511578229879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24766058128513007718819919 37149087192769511578229879)
      ·
        refine ⟨55723630789154267367344819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37149087192769511578229879 55723630789154267367344819)
        ·
          refine ⟨83585446183731401051017229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55723630789154267367344819 83585446183731401051017229)
          ·
            refine ⟨31344542318899275394131461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83585446183731401051017229 31344542318899275394131461)
            ·
              refine ⟨5877101684793614136399649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31344542318899275394131461 5877101684793614136399649)
              ·
                refine ⟨4407826263595210602299737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877101684793614136399649 4407826263595210602299737)
                ·
                  refine ⟨3305869697696407951724803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407826263595210602299737 3305869697696407951724803)
                  ·
                    refine ⟨4958804546544611927587205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3305869697696407951724803 4958804546544611927587205)
                    ·
                      refine ⟨929775852477114736422601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4958804546544611927587205 929775852477114736422601)
                      ·
                        rfl

theorem cell23_1810732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_1810732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810732 prefixEnd_1810732 := by exact prefixLift 1810732
  have htrace : WordTrace (prefixWord ++ tailWord_1810732) baseStart_1810732 baseEnd_1810732 := by
    simpa [prefixWord, tailWord_1810732, baseEnd_1810732] using wordTrace_append hprefix tailTrace_1810732
  have hstable : (prefixWord ++ tailWord_1810732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810732).length < 2 ^ (prefixWord ++ tailWord_1810732).sum := by decide
  have hdescent : baseEnd_1810732 < baseStart_1810732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810769 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_1810769 : Nat := 118140960795 + 1810769 * 2 ^ 59
def prefixEnd_1810769 : Nat := 4983230072969 + 3 ^ 40 * 1810769 * 2
def baseEnd_1810769 : Nat := 929794851261331091659931

theorem tailTrace_1810769 : CollatzResearch.WordTrace tailWord_1810769 prefixEnd_1810769 929794851261331091659931 := by
  unfold tailWord_1810769
  simp only [CollatzResearch.WordTrace]
  refine ⟨66044171176900642569283361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44029447451267095046188907 66044171176900642569283361)
  ·
    refine ⟨49533128382675481926962521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66044171176900642569283361 49533128382675481926962521)
    ·
      refine ⟨37149846287006611445221891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49533128382675481926962521 37149846287006611445221891)
      ·
        refine ⟨55724769430509917167832837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37149846287006611445221891 55724769430509917167832837)
        ·
          refine ⟨10448394268220609468968657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55724769430509917167832837 10448394268220609468968657)
          ·
            refine ⟨7836295701165457101726493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448394268220609468968657 7836295701165457101726493)
            ·
              refine ⟨2938610887937046413147435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7836295701165457101726493 2938610887937046413147435)
              ·
                refine ⟨4407916331905569619721153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938610887937046413147435 4407916331905569619721153)
                ·
                  refine ⟨3305937248929177214790865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407916331905569619721153 3305937248929177214790865)
                  ·
                    refine ⟨2479452936696882911093149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3305937248929177214790865 2479452936696882911093149)
                    ·
                      refine ⟨929794851261331091659931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479452936696882911093149 929794851261331091659931)
                      ·
                        rfl

theorem cell23_1810769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_1810769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810769 prefixEnd_1810769 := by exact prefixLift 1810769
  have htrace : WordTrace (prefixWord ++ tailWord_1810769) baseStart_1810769 baseEnd_1810769 := by
    simpa [prefixWord, tailWord_1810769, baseEnd_1810769] using wordTrace_append hprefix tailTrace_1810769
  have hstable : (prefixWord ++ tailWord_1810769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810769).length < 2 ^ (prefixWord ++ tailWord_1810769).sum := by decide
  have hdescent : baseEnd_1810769 < baseStart_1810769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810789 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 6]
def baseStart_1810789 : Nat := 118140960795 + 1810789 * 2 ^ 59
def prefixEnd_1810789 : Nat := 4983230072969 + 3 ^ 40 * 1810789 * 2
def baseEnd_1810789 : Nat := 103311680097157890378871

theorem tailTrace_1810789 : CollatzResearch.WordTrace tailWord_1810789 prefixEnd_1810789 103311680097157890378871 := by
  unfold tailWord_1810789
  simp only [CollatzResearch.WordTrace]
  refine ⟨66044900636828185985011421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44029933757885457323340947 66044900636828185985011421)
  ·
    refine ⟨24766837738810569744379283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66044900636828185985011421 24766837738810569744379283)
    ·
      refine ⟨37150256608215854616568925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24766837738810569744379283 37150256608215854616568925)
      ·
        refine ⟨13931346228080945481213347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37150256608215854616568925 13931346228080945481213347)
        ·
          refine ⟨20897019342121418221820021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13931346228080945481213347 20897019342121418221820021)
          ·
            refine ⟨1959095563323882958295627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20897019342121418221820021 1959095563323882958295627)
            ·
              refine ⟨2938643344985824437443441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959095563323882958295627 2938643344985824437443441)
              ·
                refine ⟨2203982508739368328082581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938643344985824437443441 2203982508739368328082581)
                ·
                  refine ⟨103311680097157890378871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2203982508739368328082581 103311680097157890378871)
                  ·
                    rfl

theorem cell23_1810789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_1810789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810789 prefixEnd_1810789 := by exact prefixLift 1810789
  have htrace : WordTrace (prefixWord ++ tailWord_1810789) baseStart_1810789 baseEnd_1810789 := by
    simpa [prefixWord, tailWord_1810789, baseEnd_1810789] using wordTrace_append hprefix tailTrace_1810789
  have hstable : (prefixWord ++ tailWord_1810789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810789).length < 2 ^ (prefixWord ++ tailWord_1810789).sum := by decide
  have hdescent : baseEnd_1810789 < baseStart_1810789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810792 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1810792 : Nat := 118140960795 + 1810792 * 2 ^ 59
def prefixEnd_1810792 : Nat := 4983230072969 + 3 ^ 40 * 1810792 * 2
def baseEnd_1810792 : Nat := 929806661316384501672325

theorem tailTrace_1810792 : CollatzResearch.WordTrace tailWord_1810792 prefixEnd_1810792 929806661316384501672325 := by
  unfold tailWord_1810792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33022505027908658748685315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44030006703878211664913753 33022505027908658748685315)
  ·
    refine ⟨49533757541862988123027973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33022505027908658748685315 49533757541862988123027973)
    ·
      refine ⟨9287579539099310273067745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49533757541862988123027973 9287579539099310273067745)
      ·
        refine ⟨6965684654324482704800809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9287579539099310273067745 6965684654324482704800809)
        ·
          refine ⟨5224263490743362028600607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6965684654324482704800809 5224263490743362028600607)
          ·
            refine ⟨7836395236115043042900911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224263490743362028600607 7836395236115043042900911)
            ·
              refine ⟨11754592854172564564351367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836395236115043042900911 11754592854172564564351367)
              ·
                refine ⟨17631889281258846846527051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11754592854172564564351367 17631889281258846846527051)
                ·
                  refine ⟨26447833921888270269790577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17631889281258846846527051 26447833921888270269790577)
                  ·
                    refine ⟨19835875441416202702342933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26447833921888270269790577 19835875441416202702342933)
                    ·
                      refine ⟨929806661316384501672325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19835875441416202702342933 929806661316384501672325)
                      ·
                        rfl

theorem cell23_1810792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1810792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810792 prefixEnd_1810792 := by exact prefixLift 1810792
  have htrace : WordTrace (prefixWord ++ tailWord_1810792) baseStart_1810792 baseEnd_1810792 := by
    simpa [prefixWord, tailWord_1810792, baseEnd_1810792] using wordTrace_append hprefix tailTrace_1810792
  have hstable : (prefixWord ++ tailWord_1810792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810792).length < 2 ^ (prefixWord ++ tailWord_1810792).sum := by decide
  have hdescent : baseEnd_1810792 < baseStart_1810792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810795 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_1810795 : Nat := 118140960795 + 1810795 * 2 ^ 59
def prefixEnd_1810795 : Nat := 4983230072969 + 3 ^ 40 * 1810795 * 2
def baseEnd_1810795 : Nat := 929808201758347989934811

theorem tailTrace_1810795 : CollatzResearch.WordTrace tailWord_1810795 prefixEnd_1810795 929808201758347989934811 := by
  unfold tailWord_1810795
  simp only [CollatzResearch.WordTrace]
  refine ⟨66045119474806449009729839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44030079649870966006486559 66045119474806449009729839)
  ·
    refine ⟨99067679212209673514594759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66045119474806449009729839 99067679212209673514594759)
    ·
      refine ⟨148601518818314510271892139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99067679212209673514594759 148601518818314510271892139)
      ·
        refine ⟨222902278227471765407838209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148601518818314510271892139 222902278227471765407838209)
        ·
          refine ⟨167176708670603824055878657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222902278227471765407838209 167176708670603824055878657)
          ·
            refine ⟨125382531502952868041908993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167176708670603824055878657 125382531502952868041908993)
            ·
              refine ⟨94036898627214651031431745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125382531502952868041908993 94036898627214651031431745)
              ·
                refine ⟨70527673970410988273573809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94036898627214651031431745 70527673970410988273573809)
                ·
                  refine ⟨52895755477808241205180357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70527673970410988273573809 52895755477808241205180357)
                  ·
                    refine ⟨9917954152089045225971317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52895755477808241205180357 9917954152089045225971317)
                    ·
                      refine ⟨929808201758347989934811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9917954152089045225971317 929808201758347989934811)
                      ·
                        rfl

theorem cell23_1810795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_1810795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810795 prefixEnd_1810795 := by exact prefixLift 1810795
  have htrace : WordTrace (prefixWord ++ tailWord_1810795) baseStart_1810795 baseEnd_1810795 := by
    simpa [prefixWord, tailWord_1810795, baseEnd_1810795] using wordTrace_append hprefix tailTrace_1810795
  have hstable : (prefixWord ++ tailWord_1810795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810795).length < 2 ^ (prefixWord ++ tailWord_1810795).sum := by decide
  have hdescent : baseEnd_1810795 < baseStart_1810795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810839 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1810839 : Nat := 118140960795 + 1810839 * 2 ^ 59
def prefixEnd_1810839 : Nat := 4983230072969 + 3 ^ 40 * 1810839 * 2
def baseEnd_1810839 : Nat := 929830794907145817784609

theorem tailTrace_1810839 : CollatzResearch.WordTrace tailWord_1810839 prefixEnd_1810839 929830794907145817784609 := by
  unfold tailWord_1810839
  simp only [CollatzResearch.WordTrace]
  refine ⟨66046724286647044524331571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44031149524431363016221047 66046724286647044524331571)
  ·
    refine ⟨99070086429970566786497357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66046724286647044524331571 99070086429970566786497357)
    ·
      refine ⟨37151282411238962544936509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99070086429970566786497357 37151282411238962544936509)
      ·
        refine ⟨13931730904214610954351191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37151282411238962544936509 13931730904214610954351191)
        ·
          refine ⟨20897596356321916431526787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13931730904214610954351191 20897596356321916431526787)
          ·
            refine ⟨31346394534482874647290181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20897596356321916431526787 31346394534482874647290181)
            ·
              refine ⟨5877448975215538996366909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31346394534482874647290181 5877448975215538996366909)
              ·
                refine ⟨2204043365705827123637591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5877448975215538996366909 2204043365705827123637591)
                ·
                  refine ⟨3306065048558740685456387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204043365705827123637591 3306065048558740685456387)
                  ·
                    refine ⟨4959097572838111028184581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306065048558740685456387 4959097572838111028184581)
                    ·
                      refine ⟨929830794907145817784609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4959097572838111028184581 929830794907145817784609)
                      ·
                        rfl

theorem cell23_1810839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1810839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810839 prefixEnd_1810839 := by exact prefixLift 1810839
  have htrace : WordTrace (prefixWord ++ tailWord_1810839) baseStart_1810839 baseEnd_1810839 := by
    simpa [prefixWord, tailWord_1810839, baseEnd_1810839] using wordTrace_append hprefix tailTrace_1810839
  have hstable : (prefixWord ++ tailWord_1810839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810839).length < 2 ^ (prefixWord ++ tailWord_1810839).sum := by decide
  have hdescent : baseEnd_1810839 < baseStart_1810839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810850 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1810850 : Nat := 118140960795 + 1810850 * 2 ^ 59
def prefixEnd_1810850 : Nat := 4983230072969 + 3 ^ 40 * 1810850 * 2
def baseEnd_1810850 : Nat := 929836443194345274747059

theorem tailTrace_1810850 : CollatzResearch.WordTrace tailWord_1810850 prefixEnd_1810850 929836443194345274747059 := by
  unfold tailWord_1810850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16511781372401798350745501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44031416993071462268654669 16511781372401798350745501)
  ·
    refine ⟨6191918014650674381529563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16511781372401798350745501 6191918014650674381529563)
    ·
      refine ⟨9287877021976011572294345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191918014650674381529563 9287877021976011572294345)
      ·
        refine ⟨6965907766482008679220759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9287877021976011572294345 6965907766482008679220759)
        ·
          refine ⟨10448861649723013018831139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965907766482008679220759 10448861649723013018831139)
          ·
            refine ⟨15673292474584519528246709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448861649723013018831139 15673292474584519528246709)
            ·
              refine ⟨1469371169492298705773129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15673292474584519528246709 1469371169492298705773129)
              ·
                refine ⟨1102028377119224029329847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469371169492298705773129 1102028377119224029329847)
                ·
                  refine ⟨1653042565678836043994771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102028377119224029329847 1653042565678836043994771)
                  ·
                    refine ⟨2479563848518254065992157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653042565678836043994771 2479563848518254065992157)
                    ·
                      refine ⟨929836443194345274747059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479563848518254065992157 929836443194345274747059)
                      ·
                        rfl

theorem cell23_1810850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1810850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810850 prefixEnd_1810850 := by exact prefixLift 1810850
  have htrace : WordTrace (prefixWord ++ tailWord_1810850) baseStart_1810850 baseEnd_1810850 := by
    simpa [prefixWord, tailWord_1810850, baseEnd_1810850] using wordTrace_append hprefix tailTrace_1810850
  have hstable : (prefixWord ++ tailWord_1810850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810850).length < 2 ^ (prefixWord ++ tailWord_1810850).sum := by decide
  have hdescent : baseEnd_1810850 < baseStart_1810850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810852 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1810852 : Nat := 118140960795 + 1810852 * 2 ^ 59
def prefixEnd_1810852 : Nat := 4983230072969 + 3 ^ 40 * 1810852 * 2
def baseEnd_1810852 : Nat := 929837470155654266922049

theorem tailTrace_1810852 : CollatzResearch.WordTrace tailWord_1810852 prefixEnd_1810852 929837470155654266922049 := by
  unfold tailWord_1810852
  simp only [CollatzResearch.WordTrace]
  refine ⟨33023599217799973872277405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44031465623733298496369873 33023599217799973872277405)
  ·
    refine ⟨12383849706674990202104027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33023599217799973872277405 12383849706674990202104027)
    ·
      refine ⟨18575774560012485303156041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12383849706674990202104027 18575774560012485303156041)
      ·
        refine ⟨13931830920009363977367031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18575774560012485303156041 13931830920009363977367031)
        ·
          refine ⟨20897746380014045966050547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13931830920009363977367031 20897746380014045966050547)
          ·
            refine ⟨31346619570021068949075821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20897746380014045966050547 31346619570021068949075821)
            ·
              refine ⟨11754982338757900855903433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31346619570021068949075821 11754982338757900855903433)
              ·
                refine ⟨8816236754068425641927575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754982338757900855903433 8816236754068425641927575)
                ·
                  refine ⟨13224355131102638462891363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816236754068425641927575 13224355131102638462891363)
                  ·
                    refine ⟨19836532696653957694337045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13224355131102638462891363 19836532696653957694337045)
                    ·
                      refine ⟨929837470155654266922049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19836532696653957694337045 929837470155654266922049)
                      ·
                        rfl

theorem cell23_1810852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1810852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810852 prefixEnd_1810852 := by exact prefixLift 1810852
  have htrace : WordTrace (prefixWord ++ tailWord_1810852) baseStart_1810852 baseEnd_1810852 := by
    simpa [prefixWord, tailWord_1810852, baseEnd_1810852] using wordTrace_append hprefix tailTrace_1810852
  have hstable : (prefixWord ++ tailWord_1810852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810852).length < 2 ^ (prefixWord ++ tailWord_1810852).sum := by decide
  have hdescent : baseEnd_1810852 < baseStart_1810852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810876 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1810876 : Nat := 118140960795 + 1810876 * 2 ^ 59
def prefixEnd_1810876 : Nat := 4983230072969 + 3 ^ 40 * 1810876 * 2
def baseEnd_1810876 : Nat := 929849793691362173021939

theorem tailTrace_1810876 : CollatzResearch.WordTrace tailWord_1810876 prefixEnd_1810876 929849793691362173021939 := by
  unfold tailWord_1810876
  simp only [CollatzResearch.WordTrace]
  refine ⟨33024036893756499921714241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44032049191675333228952321 33024036893756499921714241)
  ·
    refine ⟨24768027670317374941285681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33024036893756499921714241 24768027670317374941285681)
    ·
      refine ⟨18576020752738031205964261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24768027670317374941285681 18576020752738031205964261)
      ·
        refine ⟨3483003891138380851118299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18576020752738031205964261 3483003891138380851118299)
        ·
          refine ⟨5224505836707571276677449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483003891138380851118299 5224505836707571276677449)
          ·
            refine ⟨3918379377530678457508087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224505836707571276677449 3918379377530678457508087)
            ·
              refine ⟨5877569066296017686262131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918379377530678457508087 5877569066296017686262131)
              ·
                refine ⟨8816353599444026529393197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5877569066296017686262131 8816353599444026529393197)
                ·
                  refine ⟨3306132599791509948522449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8816353599444026529393197 3306132599791509948522449)
                  ·
                    refine ⟨2479599449843632461391837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3306132599791509948522449 2479599449843632461391837)
                    ·
                      refine ⟨929849793691362173021939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479599449843632461391837 929849793691362173021939)
                      ·
                        rfl

theorem cell23_1810876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1810876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810876 prefixEnd_1810876 := by exact prefixLift 1810876
  have htrace : WordTrace (prefixWord ++ tailWord_1810876) baseStart_1810876 baseEnd_1810876 := by
    simpa [prefixWord, tailWord_1810876, baseEnd_1810876] using wordTrace_append hprefix tailTrace_1810876
  have hstable : (prefixWord ++ tailWord_1810876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810876).length < 2 ^ (prefixWord ++ tailWord_1810876).sum := by decide
  have hdescent : baseEnd_1810876 < baseStart_1810876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810889 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 3]
def baseStart_1810889 : Nat := 118140960795 + 1810889 * 2 ^ 59
def prefixEnd_1810889 : Nat := 4983230072969 + 3 ^ 40 * 1810889 * 2
def baseEnd_1810889 : Nat := 929856468939870622159379

theorem tailTrace_1810889 : CollatzResearch.WordTrace tailWord_1810889 prefixEnd_1810889 929856468939870622159379 := by
  unfold tailWord_1810889
  simp only [CollatzResearch.WordTrace]
  refine ⟨66048547936465903063651721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44032365290977268709101147 66048547936465903063651721)
  ·
    refine ⟨49536410952349427297738791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66048547936465903063651721 49536410952349427297738791)
    ·
      refine ⟨74304616428524140946608187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49536410952349427297738791 74304616428524140946608187)
      ·
        refine ⟨111456924642786211419912281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74304616428524140946608187 111456924642786211419912281)
        ·
          refine ⟨83592693482089658564934211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111456924642786211419912281 83592693482089658564934211)
          ·
            refine ⟨125389040223134487847401317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83592693482089658564934211 125389040223134487847401317)
            ·
              refine ⟨23510445041837716471387747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125389040223134487847401317 23510445041837716471387747)
              ·
                refine ⟨35265667562756574707081621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23510445041837716471387747 35265667562756574707081621)
                ·
                  refine ⟨1653078167004214439394451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35265667562756574707081621 1653078167004214439394451)
                  ·
                    refine ⟨2479617250506321659091677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653078167004214439394451 2479617250506321659091677)
                    ·
                      refine ⟨929856468939870622159379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479617250506321659091677 929856468939870622159379)
                      ·
                        rfl

theorem cell23_1810889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_1810889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810889 prefixEnd_1810889 := by exact prefixLift 1810889
  have htrace : WordTrace (prefixWord ++ tailWord_1810889) baseStart_1810889 baseEnd_1810889 := by
    simpa [prefixWord, tailWord_1810889, baseEnd_1810889] using wordTrace_append hprefix tailTrace_1810889
  have hstable : (prefixWord ++ tailWord_1810889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810889).length < 2 ^ (prefixWord ++ tailWord_1810889).sum := by decide
  have hdescent : baseEnd_1810889 < baseStart_1810889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810912 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1810912 : Nat := 118140960795 + 1810912 * 2 ^ 59
def prefixEnd_1810912 : Nat := 4983230072969 + 3 ^ 40 * 1810912 * 2
def baseEnd_1810912 : Nat := 929868278994924032171773

theorem tailTrace_1810912 : CollatzResearch.WordTrace tailWord_1810912 prefixEnd_1810912 929868278994924032171773 := by
  unfold tailWord_1810912
  simp only [CollatzResearch.WordTrace]
  refine ⟨33024693407691288995869495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44032924543588385327825993 33024693407691288995869495)
  ·
    refine ⟨49537040111536933493804243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33024693407691288995869495 49537040111536933493804243)
    ·
      refine ⟨74305560167305400240706365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49537040111536933493804243 74305560167305400240706365)
      ·
        refine ⟨27864585062739525090264887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74305560167305400240706365 27864585062739525090264887)
        ·
          refine ⟨41796877594109287635397331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27864585062739525090264887 41796877594109287635397331)
          ·
            refine ⟨62695316391163931453095997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41796877594109287635397331 62695316391163931453095997)
            ·
              refine ⟨23510743646686474294910999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62695316391163931453095997 23510743646686474294910999)
              ·
                refine ⟨35266115470029711442366499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23510743646686474294910999 35266115470029711442366499)
                ·
                  refine ⟨52899173205044567163549749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35266115470029711442366499 52899173205044567163549749)
                  ·
                    refine ⟨4959297487972928171582789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52899173205044567163549749 4959297487972928171582789)
                    ·
                      refine ⟨929868278994924032171773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4959297487972928171582789 929868278994924032171773)
                      ·
                        rfl

theorem cell23_1810912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1810912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810912 prefixEnd_1810912 := by exact prefixLift 1810912
  have htrace : WordTrace (prefixWord ++ tailWord_1810912) baseStart_1810912 baseEnd_1810912 := by
    simpa [prefixWord, tailWord_1810912, baseEnd_1810912] using wordTrace_append hprefix tailTrace_1810912
  have hstable : (prefixWord ++ tailWord_1810912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810912).length < 2 ^ (prefixWord ++ tailWord_1810912).sum := by decide
  have hdescent : baseEnd_1810912 < baseStart_1810912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810952 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 11]
def baseStart_1810952 : Nat := 118140960795 + 1810952 * 2 ^ 59
def prefixEnd_1810952 : Nat := 4983230072969 + 3 ^ 40 * 1810952 * 2
def baseEnd_1810952 : Nat := 103320979802344875074621

theorem tailTrace_1810952 : CollatzResearch.WordTrace tailWord_1810952 prefixEnd_1810952 103320979802344875074621 := by
  unfold tailWord_1810952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33025422867618832411597555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44033897156825109882130073 33025422867618832411597555)
  ·
    refine ⟨49538134301428248617396333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33025422867618832411597555 49538134301428248617396333)
    ·
      refine ⟨18576800363035593231523625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49538134301428248617396333 18576800363035593231523625)
      ·
        refine ⟨13932600272276694923642719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18576800363035593231523625 13932600272276694923642719)
        ·
          refine ⟨20898900408415042385464079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13932600272276694923642719 20898900408415042385464079)
          ·
            refine ⟨31348350612622563578196119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20898900408415042385464079 31348350612622563578196119)
            ·
              refine ⟨47022525918933845367294179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31348350612622563578196119 47022525918933845367294179)
              ·
                refine ⟨70533788878400768050941269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47022525918933845367294179 70533788878400768050941269)
                ·
                  refine ⟨103320979802344875074621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 70533788878400768050941269 103320979802344875074621)
                  ·
                    rfl

theorem cell23_1810952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_1810952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810952 prefixEnd_1810952 := by exact prefixLift 1810952
  have htrace : WordTrace (prefixWord ++ tailWord_1810952) baseStart_1810952 baseEnd_1810952 := by
    simpa [prefixWord, tailWord_1810952, baseEnd_1810952] using wordTrace_append hprefix tailTrace_1810952
  have hstable : (prefixWord ++ tailWord_1810952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810952).length < 2 ^ (prefixWord ++ tailWord_1810952).sum := by decide
  have hdescent : baseEnd_1810952 < baseStart_1810952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810957 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1810957 : Nat := 118140960795 + 1810957 * 2 ^ 59
def prefixEnd_1810957 : Nat := 4983230072969 + 3 ^ 40 * 1810957 * 2
def baseEnd_1810957 : Nat := 929891385624376356109067

theorem tailTrace_1810957 : CollatzResearch.WordTrace tailWord_1810957 prefixEnd_1810957 929891385624376356109067 := by
  unfold tailWord_1810957
  simp only [CollatzResearch.WordTrace]
  refine ⟨66051028100219550677127125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44034018733479700451418083 66051028100219550677127125)
  ·
    refine ⟨1548070971098895718995167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66051028100219550677127125 1548070971098895718995167)
    ·
      refine ⟨2322106456648343578492751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548070971098895718995167 2322106456648343578492751)
      ·
        refine ⟨3483159684972515367739127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322106456648343578492751 3483159684972515367739127)
        ·
          refine ⟨5224739527458773051608691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483159684972515367739127 5224739527458773051608691)
          ·
            refine ⟨7837109291188159577413037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224739527458773051608691 7837109291188159577413037)
            ·
              refine ⟨2938915984195559841529889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7837109291188159577413037 2938915984195559841529889)
              ·
                refine ⟨2204186988146669881147417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2938915984195559841529889 2204186988146669881147417)
                ·
                  refine ⟨1653140241110002410860563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204186988146669881147417 1653140241110002410860563)
                  ·
                    refine ⟨2479710361665003616290845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653140241110002410860563 2479710361665003616290845)
                    ·
                      refine ⟨929891385624376356109067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479710361665003616290845 929891385624376356109067)
                      ·
                        rfl

theorem cell23_1810957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1810957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810957 prefixEnd_1810957 := by exact prefixLift 1810957
  have htrace : WordTrace (prefixWord ++ tailWord_1810957) baseStart_1810957 baseEnd_1810957 := by
    simpa [prefixWord, tailWord_1810957, baseEnd_1810957] using wordTrace_append hprefix tailTrace_1810957
  have hstable : (prefixWord ++ tailWord_1810957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810957).length < 2 ^ (prefixWord ++ tailWord_1810957).sum := by decide
  have hdescent : baseEnd_1810957 < baseStart_1810957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1810999 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 2, 5]
def baseStart_1810999 : Nat := 118140960795 + 1810999 * 2 ^ 59
def prefixEnd_1810999 : Nat := 4983230072969 + 3 ^ 40 * 1810999 * 2
def baseEnd_1810999 : Nat := 309970983937288397261291

theorem tailTrace_1810999 : CollatzResearch.WordTrace tailWord_1810999 prefixEnd_1810999 309970983937288397261291 := by
  unfold tailWord_1810999
  simp only [CollatzResearch.WordTrace]
  refine ⟨66052559966067391850156051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44035039977378261233437367 66052559966067391850156051)
  ·
    refine ⟨99078839949101087775234077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66052559966067391850156051 99078839949101087775234077)
    ·
      refine ⟨37154564980912907915712779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99078839949101087775234077 37154564980912907915712779)
      ·
        refine ⟨55731847471369361873569169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37154564980912907915712779 55731847471369361873569169)
        ·
          refine ⟨41798885603527021405176877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55731847471369361873569169 41798885603527021405176877)
          ·
            refine ⟨15674582101322633026941329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41798885603527021405176877 15674582101322633026941329)
            ·
              refine ⟨11755936575991974770205997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15674582101322633026941329 11755936575991974770205997)
              ·
                refine ⟨4408476215996990538827249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755936575991974770205997 4408476215996990538827249)
                ·
                  refine ⟨3306357161997742904120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408476215996990538827249 3306357161997742904120437)
                  ·
                    refine ⟨309970983937288397261291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3306357161997742904120437 309970983937288397261291)
                    ·
                      rfl

theorem cell23_1810999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_1810999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1810999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1810999 prefixEnd_1810999 := by exact prefixLift 1810999
  have htrace : WordTrace (prefixWord ++ tailWord_1810999) baseStart_1810999 baseEnd_1810999 := by
    simpa [prefixWord, tailWord_1810999, baseEnd_1810999] using wordTrace_append hprefix tailTrace_1810999
  have hstable : (prefixWord ++ tailWord_1810999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1810999).length < 2 ^ (prefixWord ++ tailWord_1810999).sum := by decide
  have hdescent : baseEnd_1810999 < baseStart_1810999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1810999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811019 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4]
def baseStart_1811019 : Nat := 118140960795 + 1811019 * 2 ^ 59
def prefixEnd_1811019 : Nat := 4983230072969 + 3 ^ 40 * 1811019 * 2
def baseEnd_1811019 : Nat := 929923221424955113533781

theorem tailTrace_1811019 : CollatzResearch.WordTrace tailWord_1811019 prefixEnd_1811019 929923221424955113533781 := by
  unfold tailWord_1811019
  simp only [CollatzResearch.WordTrace]
  refine ⟨66053289425994935265884111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44035526283996623510589407 66053289425994935265884111)
  ·
    refine ⟨99079934138992402898826167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66053289425994935265884111 99079934138992402898826167)
    ·
      refine ⟨148619901208488604348239251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99079934138992402898826167 148619901208488604348239251)
      ·
        refine ⟨222929851812732906522358877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148619901208488604348239251 222929851812732906522358877)
        ·
          refine ⟨83598694429774839945884579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222929851812732906522358877 83598694429774839945884579)
          ·
            refine ⟨125398041644662259918826869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83598694429774839945884579 125398041644662259918826869)
            ·
              refine ⟨11756066404187086867390019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125398041644662259918826869 11756066404187086867390019)
              ·
                refine ⟨17634099606280630301085029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11756066404187086867390019 17634099606280630301085029)
                ·
                  refine ⟨3306393676177618181453443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17634099606280630301085029 3306393676177618181453443)
                  ·
                    refine ⟨4959590514266427272180165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306393676177618181453443 4959590514266427272180165)
                    ·
                      refine ⟨929923221424955113533781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4959590514266427272180165 929923221424955113533781)
                      ·
                        rfl

theorem cell23_1811019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 4].length) (baseStart_1811019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811019 prefixEnd_1811019 := by exact prefixLift 1811019
  have htrace : WordTrace (prefixWord ++ tailWord_1811019) baseStart_1811019 baseEnd_1811019 := by
    simpa [prefixWord, tailWord_1811019, baseEnd_1811019] using wordTrace_append hprefix tailTrace_1811019
  have hstable : (prefixWord ++ tailWord_1811019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811019).length < 2 ^ (prefixWord ++ tailWord_1811019).sum := by decide
  have hdescent : baseEnd_1811019 < baseStart_1811019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811039 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1811039 : Nat := 118140960795 + 1811039 * 2 ^ 59
def prefixEnd_1811039 : Nat := 4983230072969 + 3 ^ 40 * 1811039 * 2
def baseEnd_1811039 : Nat := 929933491038045035283689

theorem tailTrace_1811039 : CollatzResearch.WordTrace tailWord_1811039 prefixEnd_1811039 929933491038045035283689 := by
  unfold tailWord_1811039
  simp only [CollatzResearch.WordTrace]
  refine ⟨66054018885922478681612171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44036012590614985787741447 66054018885922478681612171)
  ·
    refine ⟨99081028328883718022418257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66054018885922478681612171 99081028328883718022418257)
    ·
      refine ⟨74310771246662788516813693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99081028328883718022418257 74310771246662788516813693)
      ·
        refine ⟨27866539217498545693805135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74310771246662788516813693 27866539217498545693805135)
        ·
          refine ⟨41799808826247818540707703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27866539217498545693805135 41799808826247818540707703)
          ·
            refine ⟨62699713239371727811061555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41799808826247818540707703 62699713239371727811061555)
            ·
              refine ⟨94049569859057591716592333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62699713239371727811061555 94049569859057591716592333)
              ·
                refine ⟨35268588697146596893722125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94049569859057591716592333 35268588697146596893722125)
                ·
                  refine ⟨13225720761429973835145797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35268588697146596893722125 13225720761429973835145797)
                  ·
                    refine ⟨2479822642768120094089837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13225720761429973835145797 2479822642768120094089837)
                    ·
                      refine ⟨929933491038045035283689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2479822642768120094089837 929933491038045035283689)
                      ·
                        rfl

theorem cell23_1811039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1811039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811039 prefixEnd_1811039 := by exact prefixLift 1811039
  have htrace : WordTrace (prefixWord ++ tailWord_1811039) baseStart_1811039 baseEnd_1811039 := by
    simpa [prefixWord, tailWord_1811039, baseEnd_1811039] using wordTrace_append hprefix tailTrace_1811039
  have hstable : (prefixWord ++ tailWord_1811039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811039).length < 2 ^ (prefixWord ++ tailWord_1811039).sum := by decide
  have hdescent : baseEnd_1811039 < baseStart_1811039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811053 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1811053 : Nat := 118140960795 + 1811053 * 2 ^ 59
def prefixEnd_1811053 : Nat := 4983230072969 + 3 ^ 40 * 1811053 * 2
def baseEnd_1811053 : Nat := 929940679767207980508625

theorem tailTrace_1811053 : CollatzResearch.WordTrace tailWord_1811053 prefixEnd_1811053 929940679767207980508625 := by
  unfold tailWord_1811053
  simp only [CollatzResearch.WordTrace]
  refine ⟨66054529507871759072621813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44036353005247839381747875 66054529507871759072621813)
  ·
    refine ⟨6192612141362977413058295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66054529507871759072621813 6192612141362977413058295)
    ·
      refine ⟨9288918212044466119587443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6192612141362977413058295 9288918212044466119587443)
      ·
        refine ⟨13933377318066699179381165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9288918212044466119587443 13933377318066699179381165)
        ·
          refine ⟨5225016494275012192267937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13933377318066699179381165 5225016494275012192267937)
          ·
            refine ⟨3918762370706259144200953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225016494275012192267937 3918762370706259144200953)
            ·
              refine ⟨2939071778029694358150715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918762370706259144200953 2939071778029694358150715)
              ·
                refine ⟨4408607667044541537226073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939071778029694358150715 4408607667044541537226073)
                ·
                  refine ⟨3306455750283406152919555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408607667044541537226073 3306455750283406152919555)
                  ·
                    refine ⟨4959683625425109229379333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306455750283406152919555 4959683625425109229379333)
                    ·
                      refine ⟨929940679767207980508625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4959683625425109229379333 929940679767207980508625)
                      ·
                        rfl

theorem cell23_1811053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1811053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811053 prefixEnd_1811053 := by exact prefixLift 1811053
  have htrace : WordTrace (prefixWord ++ tailWord_1811053) baseStart_1811053 baseEnd_1811053 := by
    simpa [prefixWord, tailWord_1811053, baseEnd_1811053] using wordTrace_append hprefix tailTrace_1811053
  have hstable : (prefixWord ++ tailWord_1811053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811053).length < 2 ^ (prefixWord ++ tailWord_1811053).sum := by decide
  have hdescent : baseEnd_1811053 < baseStart_1811053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811076 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 6]
def baseStart_1811076 : Nat := 118140960795 + 1811076 * 2 ^ 59
def prefixEnd_1811076 : Nat := 4983230072969 + 3 ^ 40 * 1811076 * 2
def baseEnd_1811076 : Nat := 103328054424695710057891

theorem tailTrace_1811076 : CollatzResearch.WordTrace tailWord_1811076 prefixEnd_1811076 103328054424695710057891 := by
  unfold tailWord_1811076
  simp only [CollatzResearch.WordTrace]
  refine ⟨33027684193394217000354541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44036912257858956000472721 33027684193394217000354541)
  ·
    refine ⟨12385381572522831375132953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33027684193394217000354541 12385381572522831375132953)
    ·
      refine ⟨9289036179392123531349715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12385381572522831375132953 9289036179392123531349715)
      ·
        refine ⟨13933554269088185297024573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289036179392123531349715 13933554269088185297024573)
        ·
          refine ⟨5225082850908069486384215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13933554269088185297024573 5225082850908069486384215)
          ·
            refine ⟨7837624276362104229576323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225082850908069486384215 7837624276362104229576323)
            ·
              refine ⟨11756436414543156344364485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837624276362104229576323 11756436414543156344364485)
              ·
                refine ⟨2204331827726841814568341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11756436414543156344364485 2204331827726841814568341)
                ·
                  refine ⟨103328054424695710057891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2204331827726841814568341 103328054424695710057891)
                  ·
                    rfl

theorem cell23_1811076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_1811076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811076 prefixEnd_1811076 := by exact prefixLift 1811076
  have htrace : WordTrace (prefixWord ++ tailWord_1811076) baseStart_1811076 baseEnd_1811076 := by
    simpa [prefixWord, tailWord_1811076, baseEnd_1811076] using wordTrace_append hprefix tailTrace_1811076
  have hstable : (prefixWord ++ tailWord_1811076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811076).length < 2 ^ (prefixWord ++ tailWord_1811076).sum := by decide
  have hdescent : baseEnd_1811076 < baseStart_1811076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811079 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1811079 : Nat := 118140960795 + 1811079 * 2 ^ 59
def prefixEnd_1811079 : Nat := 4983230072969 + 3 ^ 40 * 1811079 * 2
def baseEnd_1811079 : Nat := 929954030264224878783505

theorem tailTrace_1811079 : CollatzResearch.WordTrace tailWord_1811079 prefixEnd_1811079 929954030264224878783505 := by
  unfold tailWord_1811079
  simp only [CollatzResearch.WordTrace]
  refine ⟨66055477805777565513068291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44036985203851710342045527 66055477805777565513068291)
  ·
    refine ⟨99083216708666348269602437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66055477805777565513068291 99083216708666348269602437)
    ·
      refine ⟨18578103132874940300550457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99083216708666348269602437 18578103132874940300550457)
      ·
        refine ⟨13933577349656205225412843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18578103132874940300550457 13933577349656205225412843)
        ·
          refine ⟨20900366024484307838119265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13933577349656205225412843 20900366024484307838119265)
          ·
            refine ⟨15675274518363230878589449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20900366024484307838119265 15675274518363230878589449)
            ·
              refine ⟨11756455888772423158942087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15675274518363230878589449 11756455888772423158942087)
              ·
                refine ⟨17634683833158634738413131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11756455888772423158942087 17634683833158634738413131)
                ·
                  refine ⟨26452025749737952107619697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17634683833158634738413131 26452025749737952107619697)
                  ·
                    refine ⟨19839019312303464080714773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26452025749737952107619697 19839019312303464080714773)
                    ·
                      refine ⟨929954030264224878783505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19839019312303464080714773 929954030264224878783505)
                      ·
                        rfl

theorem cell23_1811079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1811079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811079 prefixEnd_1811079 := by exact prefixLift 1811079
  have htrace : WordTrace (prefixWord ++ tailWord_1811079) baseStart_1811079 baseEnd_1811079 := by
    simpa [prefixWord, tailWord_1811079, baseEnd_1811079] using wordTrace_append hprefix tailTrace_1811079
  have hstable : (prefixWord ++ tailWord_1811079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811079).length < 2 ^ (prefixWord ++ tailWord_1811079).sum := by decide
  have hdescent : baseEnd_1811079 < baseStart_1811079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811114 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1811114 : Nat := 118140960795 + 1811114 * 2 ^ 59
def prefixEnd_1811114 : Nat := 4983230072969 + 3 ^ 40 * 1811114 * 2
def baseEnd_1811114 : Nat := 309990667362377413948615

theorem tailTrace_1811114 : CollatzResearch.WordTrace tailWord_1811114 prefixEnd_1811114 309990667362377413948615 := by
  unfold tailWord_1811114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514188590162691622648099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44037836240433844327061597 16514188590162691622648099)
  ·
    refine ⟨24771282885244037433972149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16514188590162691622648099 24771282885244037433972149)
    ·
      refine ⟨2322307770491628509434889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24771282885244037433972149 2322307770491628509434889)
      ·
        refine ⟨1741730827868721382076167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2322307770491628509434889 1741730827868721382076167)
        ·
          refine ⟨2612596241803082073114251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741730827868721382076167 2612596241803082073114251)
          ·
            refine ⟨3918894362704623109671377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612596241803082073114251 3918894362704623109671377)
            ·
              refine ⟨2939170772028467332253533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918894362704623109671377 2939170772028467332253533)
              ·
                refine ⟨1102189039510675249595075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2939170772028467332253533 1102189039510675249595075)
                ·
                  refine ⟨1653283559266012874392613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102189039510675249595075 1653283559266012874392613)
                  ·
                    refine ⟨309990667362377413948615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1653283559266012874392613 309990667362377413948615)
                    ·
                      rfl

theorem cell23_1811114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1811114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811114 prefixEnd_1811114 := by exact prefixLift 1811114
  have htrace : WordTrace (prefixWord ++ tailWord_1811114) baseStart_1811114 baseEnd_1811114 := by
    simpa [prefixWord, tailWord_1811114, baseEnd_1811114] using wordTrace_append hprefix tailTrace_1811114
  have hstable : (prefixWord ++ tailWord_1811114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811114).length < 2 ^ (prefixWord ++ tailWord_1811114).sum := by decide
  have hdescent : baseEnd_1811114 < baseStart_1811114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811123 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 1, 5]
def baseStart_1811123 : Nat := 118140960795 + 1811123 * 2 ^ 59
def prefixEnd_1811123 : Nat := 4983230072969 + 3 ^ 40 * 1811123 * 2
def baseEnd_1811123 : Nat := 309992207804340902211101

theorem tailTrace_1811123 : CollatzResearch.WordTrace tailWord_1811123 prefixEnd_1811123 309992207804340902211101 := by
  unfold tailWord_1811123
  simp only [CollatzResearch.WordTrace]
  refine ⟨66057082617618161027670023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44038055078412107351780015 66057082617618161027670023)
  ·
    refine ⟨99085623926427241541505035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66057082617618161027670023 99085623926427241541505035)
    ·
      refine ⟨148628435889640862312257553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99085623926427241541505035 148628435889640862312257553)
      ·
        refine ⟨111471326917230646734193165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148628435889640862312257553 111471326917230646734193165)
        ·
          refine ⟨41801747593961492525322437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111471326917230646734193165 41801747593961492525322437)
          ·
            refine ⟨7837827673867779848497957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41801747593961492525322437 7837827673867779848497957)
            ·
              refine ⟨1469592688850208721593367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7837827673867779848497957 1469592688850208721593367)
              ·
                refine ⟨2204389033275313082390051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469592688850208721593367 2204389033275313082390051)
                ·
                  refine ⟨3306583549912969623585077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204389033275313082390051 3306583549912969623585077)
                  ·
                    refine ⟨309992207804340902211101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3306583549912969623585077 309992207804340902211101)
                    ·
                      rfl

theorem cell23_1811123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 5].length) (baseStart_1811123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811123 prefixEnd_1811123 := by exact prefixLift 1811123
  have htrace : WordTrace (prefixWord ++ tailWord_1811123) baseStart_1811123 baseEnd_1811123 := by
    simpa [prefixWord, tailWord_1811123, baseEnd_1811123] using wordTrace_append hprefix tailTrace_1811123
  have hstable : (prefixWord ++ tailWord_1811123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811123).length < 2 ^ (prefixWord ++ tailWord_1811123).sum := by decide
  have hdescent : baseEnd_1811123 < baseStart_1811123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811139 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_1811139 : Nat := 118140960795 + 1811139 * 2 ^ 59
def prefixEnd_1811139 : Nat := 4983230072969 + 3 ^ 40 * 1811139 * 2
def baseEnd_1811139 : Nat := 929984839103494644033229

theorem tailTrace_1811139 : CollatzResearch.WordTrace tailWord_1811139 prefixEnd_1811139 929984839103494644033229 := by
  unfold tailWord_1811139
  simp only [CollatzResearch.WordTrace]
  refine ⟨66057666185560195760252471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44038444123706797173501647 66057666185560195760252471)
  ·
    refine ⟨99086499278340293640378707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66057666185560195760252471 99086499278340293640378707)
    ·
      refine ⟨148629748917510440460568061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99086499278340293640378707 148629748917510440460568061)
      ·
        refine ⟨55736155844066415172713023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148629748917510440460568061 55736155844066415172713023)
        ·
          refine ⟨83604233766099622759069535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55736155844066415172713023 83604233766099622759069535)
          ·
            refine ⟨125406350649149434138604303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83604233766099622759069535 125406350649149434138604303)
            ·
              refine ⟨188109525973724151207906455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125406350649149434138604303 188109525973724151207906455)
              ·
                refine ⟨282164288960586226811859683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188109525973724151207906455 282164288960586226811859683)
                ·
                  refine ⟨423246433440879340217789525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282164288960586226811859683 423246433440879340217789525)
                  ·
                    refine ⟨4959919141885304768177221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 423246433440879340217789525 4959919141885304768177221)
                    ·
                      refine ⟨929984839103494644033229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4959919141885304768177221 929984839103494644033229)
                      ·
                        rfl

theorem cell23_1811139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_1811139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811139 prefixEnd_1811139 := by exact prefixLift 1811139
  have htrace : WordTrace (prefixWord ++ tailWord_1811139) baseStart_1811139 baseEnd_1811139 := by
    simpa [prefixWord, tailWord_1811139, baseEnd_1811139] using wordTrace_append hprefix tailTrace_1811139
  have hstable : (prefixWord ++ tailWord_1811139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811139).length < 2 ^ (prefixWord ++ tailWord_1811139).sum := by decide
  have hdescent : baseEnd_1811139 < baseStart_1811139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811146 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1811146 : Nat := 118140960795 + 1811146 * 2 ^ 59
def prefixEnd_1811146 : Nat := 4983230072969 + 3 ^ 40 * 1811146 * 2
def baseEnd_1811146 : Nat := 929988433468076116645697

theorem tailTrace_1811146 : CollatzResearch.WordTrace tailWord_1811146 prefixEnd_1811146 929988433468076116645697 := by
  unfold tailWord_1811146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514480374133708988939323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44038614331023223970504861 16514480374133708988939323)
  ·
    refine ⟨24771720561200563483408985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16514480374133708988939323 24771720561200563483408985)
    ·
      refine ⟨18578790420900422612556739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24771720561200563483408985 18578790420900422612556739)
      ·
        refine ⟨27868185631350633918835109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18578790420900422612556739 27868185631350633918835109)
        ·
          refine ⟨5225284805878243859781583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27868185631350633918835109 5225284805878243859781583)
          ·
            refine ⟨7837927208817365789672375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225284805878243859781583 7837927208817365789672375)
            ·
              refine ⟨11756890813226048684508563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837927208817365789672375 11756890813226048684508563)
              ·
                refine ⟨17635336219839073026762845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11756890813226048684508563 17635336219839073026762845)
                ·
                  refine ⟨6613251082439652385036067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17635336219839073026762845 6613251082439652385036067)
                  ·
                    refine ⟨9919876623659478577554101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6613251082439652385036067 9919876623659478577554101)
                    ·
                      refine ⟨929988433468076116645697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9919876623659478577554101 929988433468076116645697)
                      ·
                        rfl

theorem cell23_1811146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1811146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811146 prefixEnd_1811146 := by exact prefixLift 1811146
  have htrace : WordTrace (prefixWord ++ tailWord_1811146) baseStart_1811146 baseEnd_1811146 := by
    simpa [prefixWord, tailWord_1811146, baseEnd_1811146] using wordTrace_append hprefix tailTrace_1811146
  have hstable : (prefixWord ++ tailWord_1811146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811146).length < 2 ^ (prefixWord ++ tailWord_1811146).sum := by decide
  have hdescent : baseEnd_1811146 < baseStart_1811146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811160 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_1811160 : Nat := 118140960795 + 1811160 * 2 ^ 59
def prefixEnd_1811160 : Nat := 4983230072969 + 3 ^ 40 * 1811160 * 2
def baseEnd_1811160 : Nat := 929995622197239061870633

theorem tailTrace_1811160 : CollatzResearch.WordTrace tailWord_1811160 prefixEnd_1811160 929995622197239061870633 := by
  unfold tailWord_1811160
  simp only [CollatzResearch.WordTrace]
  refine ⟨33029216059242058173383467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44038954745656077564511289 33029216059242058173383467)
  ·
    refine ⟨49543824088863087260075201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33029216059242058173383467 49543824088863087260075201)
    ·
      refine ⟨37157868066647315445056401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49543824088863087260075201 37157868066647315445056401)
      ·
        refine ⟨27868401049985486583792301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37157868066647315445056401 27868401049985486583792301)
        ·
          refine ⟨10450650393744557468922113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27868401049985486583792301 10450650393744557468922113)
          ·
            refine ⟨7837987795308418101691585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450650393744557468922113 7837987795308418101691585)
            ·
              refine ⟨5878490846481313576268689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7837987795308418101691585 5878490846481313576268689)
              ·
                refine ⟨4408868134860985182201517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5878490846481313576268689 4408868134860985182201517)
                ·
                  refine ⟨1653325550572869443325569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4408868134860985182201517 1653325550572869443325569)
                  ·
                    refine ⟨1239994162929652082494177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1653325550572869443325569 1239994162929652082494177)
                    ·
                      refine ⟨929995622197239061870633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1239994162929652082494177 929995622197239061870633)
                      ·
                        rfl

theorem cell23_1811160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_1811160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811160 prefixEnd_1811160 := by exact prefixLift 1811160
  have htrace : WordTrace (prefixWord ++ tailWord_1811160) baseStart_1811160 baseEnd_1811160 := by
    simpa [prefixWord, tailWord_1811160, baseEnd_1811160] using wordTrace_append hprefix tailTrace_1811160
  have hstable : (prefixWord ++ tailWord_1811160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811160).length < 2 ^ (prefixWord ++ tailWord_1811160).sum := by decide
  have hdescent : baseEnd_1811160 < baseStart_1811160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811177 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 1, 2, 2]
def baseStart_1811177 : Nat := 118140960795 + 1811177 * 2 ^ 59
def prefixEnd_1811177 : Nat := 4983230072969 + 3 ^ 40 * 1811177 * 2
def baseEnd_1811177 : Nat := 930004351368365495358055

theorem tailTrace_1811177 : CollatzResearch.WordTrace tailWord_1811177 prefixEnd_1811177 930004351368365495358055 := by
  unfold tailWord_1811177
  simp only [CollatzResearch.WordTrace]
  refine ⟨66059052159422528250135785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44039368106281685500090523 66059052159422528250135785)
  ·
    refine ⟨49544289119566896187601839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66059052159422528250135785 49544289119566896187601839)
    ·
      refine ⟨74316433679350344281402759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49544289119566896187601839 74316433679350344281402759)
      ·
        refine ⟨111474650519025516422104139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74316433679350344281402759 111474650519025516422104139)
        ·
          refine ⟨167211975778538274633156209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111474650519025516422104139 167211975778538274633156209)
          ·
            refine ⟨125408981833903705974867157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167211975778538274633156209 125408981833903705974867157)
            ·
              refine ⟨2939273011732118108785949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125408981833903705974867157 2939273011732118108785949)
              ·
                refine ⟨1102227379399544290794731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2939273011732118108785949 1102227379399544290794731)
                ·
                  refine ⟨1653341069099316436192097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102227379399544290794731 1653341069099316436192097)
                  ·
                    refine ⟨1240005801824487327144073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1653341069099316436192097 1240005801824487327144073)
                    ·
                      refine ⟨930004351368365495358055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240005801824487327144073 930004351368365495358055)
                      ·
                        rfl

theorem cell23_1811177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 2, 2].length) (baseStart_1811177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811177 prefixEnd_1811177 := by exact prefixLift 1811177
  have htrace : WordTrace (prefixWord ++ tailWord_1811177) baseStart_1811177 baseEnd_1811177 := by
    simpa [prefixWord, tailWord_1811177, baseEnd_1811177] using wordTrace_append hprefix tailTrace_1811177
  have hstable : (prefixWord ++ tailWord_1811177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811177).length < 2 ^ (prefixWord ++ tailWord_1811177).sum := by decide
  have hdescent : baseEnd_1811177 < baseStart_1811177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811179 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 9]
def baseStart_1811179 : Nat := 118140960795 + 1811179 * 2 ^ 59
def prefixEnd_1811179 : Nat := 4983230072969 + 3 ^ 40 * 1811179 * 2
def baseEnd_1811179 : Nat := 310001792776558162511015

theorem tailTrace_1811179 : CollatzResearch.WordTrace tailWord_1811179 prefixEnd_1811179 310001792776558162511015 := by
  unfold tailWord_1811179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66059125105415282591708591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44039416736943521727805727 66059125105415282591708591)
  ·
    refine ⟨99088687658122923887562887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66059125105415282591708591 99088687658122923887562887)
    ·
      refine ⟨148633031487184385831344331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99088687658122923887562887 148633031487184385831344331)
      ·
        refine ⟨222949547230776578747016497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148633031487184385831344331 222949547230776578747016497)
        ·
          refine ⟨167212160423082434060262373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222949547230776578747016497 167212160423082434060262373)
          ·
            refine ⟨31352280079327956386299195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167212160423082434060262373 31352280079327956386299195)
            ·
              refine ⟨47028420118991934579448793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31352280079327956386299195 47028420118991934579448793)
              ·
                refine ⟨35271315089243950934586595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47028420118991934579448793 35271315089243950934586595)
                ·
                  refine ⟨52906972633865926401879893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35271315089243950934586595 52906972633865926401879893)
                  ·
                    refine ⟨310001792776558162511015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 52906972633865926401879893 310001792776558162511015)
                    ·
                      rfl

theorem cell23_1811179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_1811179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811179 prefixEnd_1811179 := by exact prefixLift 1811179
  have htrace : WordTrace (prefixWord ++ tailWord_1811179) baseStart_1811179 baseEnd_1811179 := by
    simpa [prefixWord, tailWord_1811179, baseEnd_1811179] using wordTrace_append hprefix tailTrace_1811179
  have hstable : (prefixWord ++ tailWord_1811179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811179).length < 2 ^ (prefixWord ++ tailWord_1811179).sum := by decide
  have hdescent : baseEnd_1811179 < baseStart_1811179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811188 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1811188 : Nat := 118140960795 + 1811188 * 2 ^ 59
def prefixEnd_1811188 : Nat := 4983230072969 + 3 ^ 40 * 1811188 * 2
def baseEnd_1811188 : Nat := 930009999655564952320505

theorem tailTrace_1811188 : CollatzResearch.WordTrace tailWord_1811188 prefixEnd_1811188 930009999655564952320505 := by
  unfold tailWord_1811188
  simp only [CollatzResearch.WordTrace]
  refine ⟨33029726681191338564393109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44039635574921784752524145 33029726681191338564393109)
  ·
    refine ⟨1548268438180843995205927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33029726681191338564393109 1548268438180843995205927)
    ·
      refine ⟨2322402657271265992808891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548268438180843995205927 2322402657271265992808891)
      ·
        refine ⟨3483603985906898989213337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322402657271265992808891 3483603985906898989213337)
        ·
          refine ⟨2612702989430174241910003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3483603985906898989213337 2612702989430174241910003)
          ·
            refine ⟨3919054484145261362865005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612702989430174241910003 3919054484145261362865005)
            ·
              refine ⟨1469645431554473011074377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3919054484145261362865005 1469645431554473011074377)
              ·
                refine ⟨1102234073665854758305783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469645431554473011074377 1102234073665854758305783)
                ·
                  refine ⟨1653351110498782137458675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102234073665854758305783 1653351110498782137458675)
                  ·
                    refine ⟨2480026665748173206188013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653351110498782137458675 2480026665748173206188013)
                    ·
                      refine ⟨930009999655564952320505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480026665748173206188013 930009999655564952320505)
                      ·
                        rfl

theorem cell23_1811188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1811188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811188 prefixEnd_1811188 := by exact prefixLift 1811188
  have htrace : WordTrace (prefixWord ++ tailWord_1811188) baseStart_1811188 baseEnd_1811188 := by
    simpa [prefixWord, tailWord_1811188, baseEnd_1811188] using wordTrace_append hprefix tailTrace_1811188
  have hstable : (prefixWord ++ tailWord_1811188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811188).length < 2 ^ (prefixWord ++ tailWord_1811188).sum := by decide
  have hdescent : baseEnd_1811188 < baseStart_1811188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811203 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 3, 3, 2]
def baseStart_1811203 : Nat := 118140960795 + 1811203 * 2 ^ 59
def prefixEnd_1811203 : Nat := 4983230072969 + 3 ^ 40 * 1811203 * 2
def baseEnd_1811203 : Nat := 930017701865382393632935

theorem tailTrace_1811203 : CollatzResearch.WordTrace tailWord_1811203 prefixEnd_1811203 930017701865382393632935 := by
  unfold tailWord_1811203
  simp only [CollatzResearch.WordTrace]
  refine ⟨66060000457328334690582263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44040000304885556460388175 66060000457328334690582263)
  ·
    refine ⟨99090000685992502035873395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66060000457328334690582263 99090000685992502035873395)
    ·
      refine ⟨148635001028988753053810093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99090000685992502035873395 148635001028988753053810093)
      ·
        refine ⟨55738125385870782395178785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148635001028988753053810093 55738125385870782395178785)
        ·
          refine ⟨41803594039403086796384089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55738125385870782395178785 41803594039403086796384089)
          ·
            refine ⟨31352695529552315097288067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41803594039403086796384089 31352695529552315097288067)
            ·
              refine ⟨47029043294328472645932101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31352695529552315097288067 47029043294328472645932101)
              ·
                refine ⟨8817945617686588621112269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47029043294328472645932101 8817945617686588621112269)
                ·
                  refine ⟨3306729606632470732917101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8817945617686588621112269 3306729606632470732917101)
                  ·
                    refine ⟨1240023602487176524843913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306729606632470732917101 1240023602487176524843913)
                    ·
                      refine ⟨930017701865382393632935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240023602487176524843913 930017701865382393632935)
                      ·
                        rfl

theorem cell23_1811203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_1811203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811203 prefixEnd_1811203 := by exact prefixLift 1811203
  have htrace : WordTrace (prefixWord ++ tailWord_1811203) baseStart_1811203 baseEnd_1811203 := by
    simpa [prefixWord, tailWord_1811203, baseEnd_1811203] using wordTrace_append hprefix tailTrace_1811203
  have hstable : (prefixWord ++ tailWord_1811203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811203).length < 2 ^ (prefixWord ++ tailWord_1811203).sum := by decide
  have hdescent : baseEnd_1811203 < baseStart_1811203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811210 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1811210 : Nat := 118140960795 + 1811210 * 2 ^ 59
def prefixEnd_1811210 : Nat := 4983230072969 + 3 ^ 40 * 1811210 * 2
def baseEnd_1811210 : Nat := 930021296229963866245403

theorem tailTrace_1811210 : CollatzResearch.WordTrace tailWord_1811210 prefixEnd_1811210 930021296229963866245403 := by
  unfold tailWord_1811210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515063942075743721521771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44040170512201983257391389 16515063942075743721521771)
  ·
    refine ⟨24772595913113615582282657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16515063942075743721521771 24772595913113615582282657)
    ·
      refine ⟨18579446934835211686711993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24772595913113615582282657 18579446934835211686711993)
      ·
        refine ⟨13934585201126408765033995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18579446934835211686711993 13934585201126408765033995)
        ·
          refine ⟨20901877801689613147550993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934585201126408765033995 20901877801689613147550993)
          ·
            refine ⟨15676408351267209860663245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901877801689613147550993 15676408351267209860663245)
            ·
              refine ⟨5878653131725203697748717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15676408351267209860663245 5878653131725203697748717)
              ·
                refine ⟨2204494924396951386655769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5878653131725203697748717 2204494924396951386655769)
                ·
                  refine ⟨1653371193297713539991827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2204494924396951386655769 1653371193297713539991827)
                  ·
                    refine ⟨2480056789946570309987741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653371193297713539991827 2480056789946570309987741)
                    ·
                      refine ⟨930021296229963866245403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480056789946570309987741 930021296229963866245403)
                      ·
                        rfl

theorem cell23_1811210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1811210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811210 prefixEnd_1811210 := by exact prefixLift 1811210
  have htrace : WordTrace (prefixWord ++ tailWord_1811210) baseStart_1811210 baseEnd_1811210 := by
    simpa [prefixWord, tailWord_1811210, baseEnd_1811210] using wordTrace_append hprefix tailTrace_1811210
  have hstable : (prefixWord ++ tailWord_1811210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811210).length < 2 ^ (prefixWord ++ tailWord_1811210).sum := by decide
  have hdescent : baseEnd_1811210 < baseStart_1811210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811237 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_1811237 : Nat := 118140960795 + 1811237 * 2 ^ 59
def prefixEnd_1811237 : Nat := 4983230072969 + 3 ^ 40 * 1811237 * 2
def baseEnd_1811237 : Nat := 930035160207635260607779

theorem tailTrace_1811237 : CollatzResearch.WordTrace tailWord_1811237 prefixEnd_1811237 930035160207635260607779 := by
  unfold tailWord_1811237
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061240539205158497319965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44040827026136772331546643 66061240539205158497319965)
  ·
    refine ⟨24772965202201934436494987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66061240539205158497319965 24772965202201934436494987)
    ·
      refine ⟨37159447803302901654742481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24772965202201934436494987 37159447803302901654742481)
      ·
        refine ⟨27869585852477176241056861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37159447803302901654742481 27869585852477176241056861)
        ·
          refine ⟨10451094694678941090396323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27869585852477176241056861 10451094694678941090396323)
          ·
            refine ⟨15676642042018411635594485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451094694678941090396323 15676642042018411635594485)
            ·
              refine ⟨1469685191439226090836983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15676642042018411635594485 1469685191439226090836983)
              ·
                refine ⟨2204527787158839136255475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469685191439226090836983 2204527787158839136255475)
                ·
                  refine ⟨3306791680738258704383213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204527787158839136255475 3306791680738258704383213)
                  ·
                    refine ⟨1240046880276847014143705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3306791680738258704383213 1240046880276847014143705)
                    ·
                      refine ⟨930035160207635260607779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240046880276847014143705 930035160207635260607779)
                      ·
                        rfl

theorem cell23_1811237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_1811237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811237 prefixEnd_1811237 := by exact prefixLift 1811237
  have htrace : WordTrace (prefixWord ++ tailWord_1811237) baseStart_1811237 baseEnd_1811237 := by
    simpa [prefixWord, tailWord_1811237, baseEnd_1811237] using wordTrace_append hprefix tailTrace_1811237
  have hstable : (prefixWord ++ tailWord_1811237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811237).length < 2 ^ (prefixWord ++ tailWord_1811237).sum := by decide
  have hdescent : baseEnd_1811237 < baseStart_1811237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811245 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1811245 : Nat := 118140960795 + 1811245 * 2 ^ 59
def prefixEnd_1811245 : Nat := 4983230072969 + 3 ^ 40 * 1811245 * 2
def baseEnd_1811245 : Nat := 930039268052871229307743

theorem tailTrace_1811245 : CollatzResearch.WordTrace tailWord_1811245 prefixEnd_1811245 930039268052871229307743 := by
  unfold tailWord_1811245
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061532323176175863611189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44041021548784117242407459 66061532323176175863611189)
  ·
    refine ⟨6193268655297766487213549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66061532323176175863611189 6193268655297766487213549)
    ·
      refine ⟨2322475745736662432705081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6193268655297766487213549 2322475745736662432705081)
      ·
        refine ⟨1741856809302496824528811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2322475745736662432705081 1741856809302496824528811)
        ·
          refine ⟨2612785213953745236793217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741856809302496824528811 2612785213953745236793217)
          ·
            refine ⟨1959588910465308927594913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612785213953745236793217 1959588910465308927594913)
            ·
              refine ⟨1469691682848981695696185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959588910465308927594913 1469691682848981695696185)
              ·
                refine ⟨1102268762136736271772139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469691682848981695696185 1102268762136736271772139)
                ·
                  refine ⟨1653403143205104407658209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102268762136736271772139 1653403143205104407658209)
                  ·
                    refine ⟨1240052357403828305743657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1653403143205104407658209 1240052357403828305743657)
                    ·
                      refine ⟨930039268052871229307743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240052357403828305743657 930039268052871229307743)
                      ·
                        rfl

theorem cell23_1811245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1811245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811245 prefixEnd_1811245 := by exact prefixLift 1811245
  have htrace : WordTrace (prefixWord ++ tailWord_1811245) baseStart_1811245 baseEnd_1811245 := by
    simpa [prefixWord, tailWord_1811245, baseEnd_1811245] using wordTrace_append hprefix tailTrace_1811245
  have hstable : (prefixWord ++ tailWord_1811245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811245).length < 2 ^ (prefixWord ++ tailWord_1811245).sum := by decide
  have hdescent : baseEnd_1811245 < baseStart_1811245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811253 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1811253 : Nat := 118140960795 + 1811253 * 2 ^ 59
def prefixEnd_1811253 : Nat := 4983230072969 + 3 ^ 40 * 1811253 * 2
def baseEnd_1811253 : Nat := 930043375898107198007705

theorem tailTrace_1811253 : CollatzResearch.WordTrace tailWord_1811253 prefixEnd_1811253 930043375898107198007705 := by
  unfold tailWord_1811253
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061824107147193229902413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44041216071431462153268275 66061824107147193229902413)
  ·
    refine ⟨24773184040180197461213405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66061824107147193229902413 24773184040180197461213405)
    ·
      refine ⟨9289944015067574047955027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24773184040180197461213405 9289944015067574047955027)
      ·
        refine ⟨13934916022601361071932541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289944015067574047955027 13934916022601361071932541)
        ·
          refine ⟨5225593508475510401974703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13934916022601361071932541 5225593508475510401974703)
          ·
            refine ⟨7838390262713265602962055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225593508475510401974703 7838390262713265602962055)
            ·
              refine ⟨11757585394069898404443083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838390262713265602962055 11757585394069898404443083)
              ·
                refine ⟨17636378091104847606664625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11757585394069898404443083 17636378091104847606664625)
                ·
                  refine ⟨13227283568328635704998469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17636378091104847606664625 13227283568328635704998469)
                  ·
                    refine ⟨2480115669061619194687213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13227283568328635704998469 2480115669061619194687213)
                    ·
                      refine ⟨930043375898107198007705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480115669061619194687213 930043375898107198007705)
                      ·
                        rfl

theorem cell23_1811253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1811253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811253 prefixEnd_1811253 := by exact prefixLift 1811253
  have htrace : WordTrace (prefixWord ++ tailWord_1811253) baseStart_1811253 baseEnd_1811253 := by
    simpa [prefixWord, tailWord_1811253, baseEnd_1811253] using wordTrace_append hprefix tailTrace_1811253
  have hstable : (prefixWord ++ tailWord_1811253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811253).length < 2 ^ (prefixWord ++ tailWord_1811253).sum := by decide
  have hdescent : baseEnd_1811253 < baseStart_1811253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811256 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 7]
def baseStart_1811256 : Nat := 118140960795 + 1811256 * 2 ^ 59
def prefixEnd_1811256 : Nat := 4983230072969 + 3 ^ 40 * 1811256 * 2
def baseEnd_1811256 : Nat := 103338324037785631807799

theorem tailTrace_1811256 : CollatzResearch.WordTrace tailWord_1811256 prefixEnd_1811256 103338324037785631807799 := by
  unfold tailWord_1811256
  simp only [CollatzResearch.WordTrace]
  refine ⟨33030966763068162371130811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44041289017424216494841081 33030966763068162371130811)
  ·
    refine ⟨49546450144602243556696217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33030966763068162371130811 49546450144602243556696217)
    ·
      refine ⟨37159837608451682667522163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49546450144602243556696217 37159837608451682667522163)
      ·
        refine ⟨55739756412677524001283245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159837608451682667522163 55739756412677524001283245)
        ·
          refine ⟨20902408654754071500481217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55739756412677524001283245 20902408654754071500481217)
          ·
            refine ⟨15676806491065553625360913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20902408654754071500481217 15676806491065553625360913)
            ·
              refine ⟨11757604868299165219020685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15676806491065553625360913 11757604868299165219020685)
              ·
                refine ⟨4409101825612186957132757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11757604868299165219020685 4409101825612186957132757)
                ·
                  refine ⟨103338324037785631807799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4409101825612186957132757 103338324037785631807799)
                  ·
                    rfl

theorem cell23_1811256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_1811256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811256 prefixEnd_1811256 := by exact prefixLift 1811256
  have htrace : WordTrace (prefixWord ++ tailWord_1811256) baseStart_1811256 baseEnd_1811256 := by
    simpa [prefixWord, tailWord_1811256, baseEnd_1811256] using wordTrace_append hprefix tailTrace_1811256
  have hstable : (prefixWord ++ tailWord_1811256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811256).length < 2 ^ (prefixWord ++ tailWord_1811256).sum := by decide
  have hdescent : baseEnd_1811256 < baseStart_1811256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811263 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1811263 : Nat := 118140960795 + 1811263 * 2 ^ 59
def prefixEnd_1811263 : Nat := 4983230072969 + 3 ^ 40 * 1811263 * 2
def baseEnd_1811263 : Nat := 930048510704652158882659

theorem tailTrace_1811263 : CollatzResearch.WordTrace tailWord_1811263 prefixEnd_1811263 930048510704652158882659 := by
  unfold tailWord_1811263
  simp only [CollatzResearch.WordTrace]
  refine ⟨66062188837110964937766443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44041459224740643291844295 66062188837110964937766443)
  ·
    refine ⟨99093283255666447406649665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66062188837110964937766443 99093283255666447406649665)
    ·
      refine ⟨74319962441749835554987249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99093283255666447406649665 74319962441749835554987249)
      ·
        refine ⟨55739971831312376666240437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74319962441749835554987249 55739971831312376666240437)
        ·
          refine ⟨5225622359185535312460041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55739971831312376666240437 5225622359185535312460041)
          ·
            refine ⟨3919216769389151484345031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225622359185535312460041 3919216769389151484345031)
            ·
              refine ⟨5878825154083727226517547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919216769389151484345031 5878825154083727226517547)
              ·
                refine ⟨8818237731125590839776321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878825154083727226517547 8818237731125590839776321)
                ·
                  refine ⟨6613678298344193129832241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8818237731125590839776321 6613678298344193129832241)
                  ·
                    refine ⟨4960258723758144847374181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613678298344193129832241 4960258723758144847374181)
                    ·
                      refine ⟨930048510704652158882659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4960258723758144847374181 930048510704652158882659)
                      ·
                        rfl

theorem cell23_1811263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1811263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811263 prefixEnd_1811263 := by exact prefixLift 1811263
  have htrace : WordTrace (prefixWord ++ tailWord_1811263) baseStart_1811263 baseEnd_1811263 := by
    simpa [prefixWord, tailWord_1811263, baseEnd_1811263] using wordTrace_append hprefix tailTrace_1811263
  have hstable : (prefixWord ++ tailWord_1811263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811263).length < 2 ^ (prefixWord ++ tailWord_1811263).sum := by decide
  have hdescent : baseEnd_1811263 < baseStart_1811263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811290 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_1811290 : Nat := 118140960795 + 1811290 * 2 ^ 59
def prefixEnd_1811290 : Nat := 4983230072969 + 3 ^ 40 * 1811290 * 2
def baseEnd_1811290 : Nat := 103340263853591505916115

theorem tailTrace_1811290 : CollatzResearch.WordTrace tailWord_1811290 prefixEnd_1811290 103340263853591505916115 := by
  unfold tailWord_1811290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515793402003287137249831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44042115738675432365999549 16515793402003287137249831)
  ·
    refine ⟨24773690103004930705874747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16515793402003287137249831 24773690103004930705874747)
    ·
      refine ⟨37160535154507396058812121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24773690103004930705874747 37160535154507396058812121)
      ·
        refine ⟨27870401365880547044109091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37160535154507396058812121 27870401365880547044109091)
        ·
          refine ⟨41805602048820820566163637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27870401365880547044109091 41805602048820820566163637)
          ·
            refine ⟨3919275192076951928077841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41805602048820820566163637 3919275192076951928077841)
            ·
              refine ⟨2939456394057713946058381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919275192076951928077841 2939456394057713946058381)
              ·
                refine ⟨1102296147771642729771893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2939456394057713946058381 1102296147771642729771893)
                ·
                  refine ⟨103340263853591505916115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1102296147771642729771893 103340263853591505916115)
                  ·
                    rfl

theorem cell23_1811290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_1811290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811290 prefixEnd_1811290 := by exact prefixLift 1811290
  have htrace : WordTrace (prefixWord ++ tailWord_1811290) baseStart_1811290 baseEnd_1811290 := by
    simpa [prefixWord, tailWord_1811290, baseEnd_1811290] using wordTrace_append hprefix tailTrace_1811290
  have hstable : (prefixWord ++ tailWord_1811290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811290).length < 2 ^ (prefixWord ++ tailWord_1811290).sum := by decide
  have hdescent : baseEnd_1811290 < baseStart_1811290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811417 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 2, 3, 2]
def baseStart_1811417 : Nat := 118140960795 + 1811417 * 2 ^ 59
def prefixEnd_1811417 : Nat := 4983230072969 + 3 ^ 40 * 1811417 * 2
def baseEnd_1811417 : Nat := 930127586725444556356951

theorem tailTrace_1811417 : CollatzResearch.WordTrace tailWord_1811417 prefixEnd_1811417 930127586725444556356951 := by
  unfold tailWord_1811417
  simp only [CollatzResearch.WordTrace]
  refine ⟨66067805678553049238872505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44045203785702032825915003 66067805678553049238872505)
  ·
    refine ⟨49550854258914786929154379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66067805678553049238872505 49550854258914786929154379)
    ·
      refine ⟨74326281388372180393731569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49550854258914786929154379 74326281388372180393731569)
      ·
        refine ⟨55744711041279135295298677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74326281388372180393731569 55744711041279135295298677)
        ·
          refine ⟨5226066660119918933934251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55744711041279135295298677 5226066660119918933934251)
          ·
            refine ⟨7839099990179878400901377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226066660119918933934251 7839099990179878400901377)
            ·
              refine ⟨5879324992634908800676033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839099990179878400901377 5879324992634908800676033)
              ·
                refine ⟨4409493744476181600507025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5879324992634908800676033 4409493744476181600507025)
                ·
                  refine ⟨3307120308357136200380269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4409493744476181600507025 3307120308357136200380269)
                  ·
                    refine ⟨1240170115633926075142601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3307120308357136200380269 1240170115633926075142601)
                    ·
                      refine ⟨930127586725444556356951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240170115633926075142601 930127586725444556356951)
                      ·
                        rfl

theorem cell23_1811417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_1811417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811417 prefixEnd_1811417 := by exact prefixLift 1811417
  have htrace : WordTrace (prefixWord ++ tailWord_1811417) baseStart_1811417 baseEnd_1811417 := by
    simpa [prefixWord, tailWord_1811417, baseEnd_1811417] using wordTrace_append hprefix tailTrace_1811417
  have hstable : (prefixWord ++ tailWord_1811417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811417).length < 2 ^ (prefixWord ++ tailWord_1811417).sum := by decide
  have hdescent : baseEnd_1811417 < baseStart_1811417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811464 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_1811464 : Nat := 118140960795 + 1811464 * 2 ^ 59
def prefixEnd_1811464 : Nat := 4983230072969 + 3 ^ 40 * 1811464 * 2
def baseEnd_1811464 : Nat := 930151720316205872469235

theorem tailTrace_1811464 : CollatzResearch.WordTrace tailWord_1811464 prefixEnd_1811464 930151720316205872469235 := by
  unfold tailWord_1811464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33034759954691388132916723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44046346606255184177222297 33034759954691388132916723)
  ·
    refine ⟨49552139932037082199375085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33034759954691388132916723 49552139932037082199375085)
    ·
      refine ⟨18582052474513905824765657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49552139932037082199375085 18582052474513905824765657)
      ·
        refine ⟨13936539355885429368574243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18582052474513905824765657 13936539355885429368574243)
        ·
          refine ⟨20904809033828144052861365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13936539355885429368574243 20904809033828144052861365)
          ·
            refine ⟨1959825846921388504955753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20904809033828144052861365 1959825846921388504955753)
            ·
              refine ⟨1469869385191041378716815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959825846921388504955753 1469869385191041378716815)
              ·
                refine ⟨2204804077786562068075223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469869385191041378716815 2204804077786562068075223)
                ·
                  refine ⟨3307206116679843102112835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204804077786562068075223 3307206116679843102112835)
                  ·
                    refine ⟨4960809175019764653169253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3307206116679843102112835 4960809175019764653169253)
                    ·
                      refine ⟨930151720316205872469235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4960809175019764653169253 930151720316205872469235)
                      ·
                        rfl

theorem cell23_1811464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_1811464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811464 prefixEnd_1811464 := by exact prefixLift 1811464
  have htrace : WordTrace (prefixWord ++ tailWord_1811464) baseStart_1811464 baseEnd_1811464 := by
    simpa [prefixWord, tailWord_1811464, baseEnd_1811464] using wordTrace_append hprefix tailTrace_1811464
  have hstable : (prefixWord ++ tailWord_1811464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811464).length < 2 ^ (prefixWord ++ tailWord_1811464).sum := by decide
  have hdescent : baseEnd_1811464 < baseStart_1811464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811467 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 3]
def baseStart_1811467 : Nat := 118140960795 + 1811467 * 2 ^ 59
def prefixEnd_1811467 : Nat := 4983230072969 + 3 ^ 40 * 1811467 * 2
def baseEnd_1811467 : Nat := 930153260758169360731721

theorem tailTrace_1811467 : CollatzResearch.WordTrace tailWord_1811467 prefixEnd_1811467 930153260758169360731721 := by
  unfold tailWord_1811467
  simp only [CollatzResearch.WordTrace]
  refine ⟨66069629328371907778192655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44046419552247938518795103 66069629328371907778192655)
  ·
    refine ⟨99104443992557861667288983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66069629328371907778192655 99104443992557861667288983)
    ·
      refine ⟨148656665988836792500933475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99104443992557861667288983 148656665988836792500933475)
      ·
        refine ⟨222984998983255188751400213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148656665988836792500933475 222984998983255188751400213)
        ·
          refine ⟨10452421827340086972721885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222984998983255188751400213 10452421827340086972721885)
          ·
            refine ⟨3919658185252532614770707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10452421827340086972721885 3919658185252532614770707)
            ·
              refine ⟨5879487277878798922156061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919658185252532614770707 5879487277878798922156061)
              ·
                refine ⟨2204807729204549595808523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5879487277878798922156061 2204807729204549595808523)
                ·
                  refine ⟨3307211593806824393712785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204807729204549595808523 3307211593806824393712785)
                  ·
                    refine ⟨2480408695355118295284589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3307211593806824393712785 2480408695355118295284589)
                    ·
                      refine ⟨930153260758169360731721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480408695355118295284589 930153260758169360731721)
                      ·
                        rfl

theorem cell23_1811467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 3].length) (baseStart_1811467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811467 prefixEnd_1811467 := by exact prefixLift 1811467
  have htrace : WordTrace (prefixWord ++ tailWord_1811467) baseStart_1811467 baseEnd_1811467 := by
    simpa [prefixWord, tailWord_1811467, baseEnd_1811467] using wordTrace_append hprefix tailTrace_1811467
  have hstable : (prefixWord ++ tailWord_1811467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811467).length < 2 ^ (prefixWord ++ tailWord_1811467).sum := by decide
  have hdescent : baseEnd_1811467 < baseStart_1811467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811503 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_1811503 : Nat := 118140960795 + 1811503 * 2 ^ 59
def prefixEnd_1811503 : Nat := 4983230072969 + 3 ^ 40 * 1811503 * 2
def baseEnd_1811503 : Nat := 930171746061731219881555

theorem tailTrace_1811503 : CollatzResearch.WordTrace tailWord_1811503 prefixEnd_1811503 930171746061731219881555 := by
  unfold tailWord_1811503
  simp only [CollatzResearch.WordTrace]
  refine ⟨66070942356241485926503163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44047294904160990617668775 66070942356241485926503163)
  ·
    refine ⟨99106413534362228889754745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66070942356241485926503163 99106413534362228889754745)
    ·
      refine ⟨74329810150771671667316059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99106413534362228889754745 74329810150771671667316059)
      ·
        refine ⟨111494715226157507500974089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74329810150771671667316059 111494715226157507500974089)
        ·
          refine ⟨83621036419618130625730567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111494715226157507500974089 83621036419618130625730567)
          ·
            refine ⟨125431554629427195938595851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83621036419618130625730567 125431554629427195938595851)
            ·
              refine ⟨188147331944140793907893777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125431554629427195938595851 188147331944140793907893777)
              ·
                refine ⟨141110498958105595430920333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188147331944140793907893777 141110498958105595430920333)
                ·
                  refine ⟨52916437109289598286595125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141110498958105595430920333 52916437109289598286595125)
                  ·
                    refine ⟨4960915978995899839368293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52916437109289598286595125 4960915978995899839368293)
                    ·
                      refine ⟨930171746061731219881555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4960915978995899839368293 930171746061731219881555)
                      ·
                        rfl

theorem cell23_1811503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_1811503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811503 prefixEnd_1811503 := by exact prefixLift 1811503
  have htrace : WordTrace (prefixWord ++ tailWord_1811503) baseStart_1811503 baseEnd_1811503 := by
    simpa [prefixWord, tailWord_1811503, baseEnd_1811503] using wordTrace_append hprefix tailTrace_1811503
  have hstable : (prefixWord ++ tailWord_1811503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811503).length < 2 ^ (prefixWord ++ tailWord_1811503).sum := by decide
  have hdescent : baseEnd_1811503 < baseStart_1811503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811563 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_1811563 : Nat := 118140960795 + 1811563 * 2 ^ 59
def prefixEnd_1811563 : Nat := 4983230072969 + 3 ^ 40 * 1811563 * 2
def baseEnd_1811563 : Nat := 930202554901000985131279

theorem tailTrace_1811563 : CollatzResearch.WordTrace tailWord_1811563 prefixEnd_1811563 930202554901000985131279 := by
  unfold tailWord_1811563
  simp only [CollatzResearch.WordTrace]
  refine ⟨66073130736024116173687343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44048753824016077449124895 66073130736024116173687343)
  ·
    refine ⟨99109696104036174260531015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66073130736024116173687343 99109696104036174260531015)
    ·
      refine ⟨148664544156054261390796523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99109696104036174260531015 148664544156054261390796523)
      ·
        refine ⟨222996816234081392086194785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148664544156054261390796523 222996816234081392086194785)
        ·
          refine ⟨167247612175561044064646089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222996816234081392086194785 167247612175561044064646089)
          ·
            refine ⟨125435709131670783048484567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167247612175561044064646089 125435709131670783048484567)
            ·
              refine ⟨188153563697506174572726851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125435709131670783048484567 188153563697506174572726851)
              ·
                refine ⟨282230345546259261859090277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188153563697506174572726851 282230345546259261859090277)
                ·
                  refine ⟨52918189789923611598579427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282230345546259261859090277 52918189789923611598579427)
                  ·
                    refine ⟨79377284684885417397869141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52918189789923611598579427 79377284684885417397869141)
                    ·
                      refine ⟨930202554901000985131279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 79377284684885417397869141 930202554901000985131279)
                      ·
                        rfl

theorem cell23_1811563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_1811563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811563 prefixEnd_1811563 := by exact prefixLift 1811563
  have htrace : WordTrace (prefixWord ++ tailWord_1811563) baseStart_1811563 baseEnd_1811563 := by
    simpa [prefixWord, tailWord_1811563, baseEnd_1811563] using wordTrace_append hprefix tailTrace_1811563
  have hstable : (prefixWord ++ tailWord_1811563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811563).length < 2 ^ (prefixWord ++ tailWord_1811563).sum := by decide
  have hdescent : baseEnd_1811563 < baseStart_1811563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811644 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1811644 : Nat := 118140960795 + 1811644 * 2 ^ 59
def prefixEnd_1811644 : Nat := 4983230072969 + 3 ^ 40 * 1811644 * 2
def baseEnd_1811644 : Nat := 930244146834015168218407

theorem tailTrace_1811644 : CollatzResearch.WordTrace tailWord_1811644 prefixEnd_1811644 930244146834015168218407 := by
  unfold tailWord_1811644
  simp only [CollatzResearch.WordTrace]
  refine ⟨33038042524365333503692993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44050723365820444671590657 33038042524365333503692993)
  ·
    refine ⟨24778531893274000127769745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33038042524365333503692993 24778531893274000127769745)
    ·
      refine ⟨18583898919955500095827309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24778531893274000127769745 18583898919955500095827309)
      ·
        refine ⟨6968962094983312535935241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18583898919955500095827309 6968962094983312535935241)
        ·
          refine ⟨5226721571237484401951431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968962094983312535935241 5226721571237484401951431)
          ·
            refine ⟨7840082356856226602927147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226721571237484401951431 7840082356856226602927147)
            ·
              refine ⟨11760123535284339904390721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840082356856226602927147 11760123535284339904390721)
              ·
                refine ⟨8820092651463254928293041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11760123535284339904390721 8820092651463254928293041)
                ·
                  refine ⟨6615069488597441196219781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8820092651463254928293041 6615069488597441196219781)
                  ·
                    refine ⟨1240325529112020224291209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615069488597441196219781 1240325529112020224291209)
                    ·
                      refine ⟨930244146834015168218407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240325529112020224291209 930244146834015168218407)
                      ·
                        rfl

theorem cell23_1811644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1811644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811644 prefixEnd_1811644 := by exact prefixLift 1811644
  have htrace : WordTrace (prefixWord ++ tailWord_1811644) baseStart_1811644 baseEnd_1811644 := by
    simpa [prefixWord, tailWord_1811644, baseEnd_1811644] using wordTrace_append hprefix tailTrace_1811644
  have hstable : (prefixWord ++ tailWord_1811644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811644).length < 2 ^ (prefixWord ++ tailWord_1811644).sum := by decide
  have hdescent : baseEnd_1811644 < baseStart_1811644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811647 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1811647 : Nat := 118140960795 + 1811647 * 2 ^ 59
def prefixEnd_1811647 : Nat := 4983230072969 + 3 ^ 40 * 1811647 * 2
def baseEnd_1811647 : Nat := 930245687275978656480893

theorem tailTrace_1811647 : CollatzResearch.WordTrace tailWord_1811647 prefixEnd_1811647 930245687275978656480893 := by
  unfold tailWord_1811647
  simp only [CollatzResearch.WordTrace]
  refine ⟨66076194467719798519745195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44050796311813199013163463 66076194467719798519745195)
  ·
    refine ⟨99114291701579697779617793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66076194467719798519745195 99114291701579697779617793)
    ·
      refine ⟨74335718776184773334713345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99114291701579697779617793 74335718776184773334713345)
      ·
        refine ⟨55751789082138580001035009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74335718776184773334713345 55751789082138580001035009)
        ·
          refine ⟨41813841811603935000776257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55751789082138580001035009 41813841811603935000776257)
          ·
            refine ⟨31360381358702951250582193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41813841811603935000776257 31360381358702951250582193)
            ·
              refine ⟨23520286019027213437936645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31360381358702951250582193 23520286019027213437936645)
              ·
                refine ⟨4410053628567602519613121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23520286019027213437936645 4410053628567602519613121)
                ·
                  refine ⟨3307540221425701889709841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410053628567602519613121 3307540221425701889709841)
                  ·
                    refine ⟨2480655166069276417282381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3307540221425701889709841 2480655166069276417282381)
                    ·
                      refine ⟨930245687275978656480893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480655166069276417282381 930245687275978656480893)
                      ·
                        rfl

theorem cell23_1811647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1811647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811647 prefixEnd_1811647 := by exact prefixLift 1811647
  have htrace : WordTrace (prefixWord ++ tailWord_1811647) baseStart_1811647 baseEnd_1811647 := by
    simpa [prefixWord, tailWord_1811647, baseEnd_1811647] using wordTrace_append hprefix tailTrace_1811647
  have hstable : (prefixWord ++ tailWord_1811647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811647).length < 2 ^ (prefixWord ++ tailWord_1811647).sum := by decide
  have hdescent : baseEnd_1811647 < baseStart_1811647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811694 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_1811694 : Nat := 118140960795 + 1811694 * 2 ^ 59
def prefixEnd_1811694 : Nat := 4983230072969 + 3 ^ 40 * 1811694 * 2
def baseEnd_1811694 : Nat := 930269820866739972593177

theorem tailTrace_1811694 : CollatzResearch.WordTrace tailWord_1811694 prefixEnd_1811694 930269820866739972593177 := by
  unfold tailWord_1811694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259738587318690693338267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44051939132366350364470757 8259738587318690693338267)
  ·
    refine ⟨12389607880978036040007401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8259738587318690693338267 12389607880978036040007401)
    ·
      refine ⟨9292205910733527030005551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12389607880978036040007401 9292205910733527030005551)
      ·
        refine ⟨13938308866100290545008327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292205910733527030005551 13938308866100290545008327)
        ·
          refine ⟨20907463299150435817512491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13938308866100290545008327 20907463299150435817512491)
          ·
            refine ⟨31361194948725653726268737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20907463299150435817512491 31361194948725653726268737)
            ·
              refine ⟨23520896211544240294701553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31361194948725653726268737 23520896211544240294701553)
              ·
                refine ⟨17640672158658180221026165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23520896211544240294701553 17640672158658180221026165)
                ·
                  refine ⟨1653813014874204395721203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17640672158658180221026165 1653813014874204395721203)
                  ·
                    refine ⟨2480719522311306593581805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653813014874204395721203 2480719522311306593581805)
                    ·
                      refine ⟨930269820866739972593177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480719522311306593581805 930269820866739972593177)
                      ·
                        rfl

theorem cell23_1811694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_1811694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811694 prefixEnd_1811694 := by exact prefixLift 1811694
  have htrace : WordTrace (prefixWord ++ tailWord_1811694) baseStart_1811694 baseEnd_1811694 := by
    simpa [prefixWord, tailWord_1811694, baseEnd_1811694] using wordTrace_append hprefix tailTrace_1811694
  have hstable : (prefixWord ++ tailWord_1811694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811694).length < 2 ^ (prefixWord ++ tailWord_1811694).sum := by decide
  have hdescent : baseEnd_1811694 < baseStart_1811694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811711 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 3]
def baseStart_1811711 : Nat := 118140960795 + 1811711 * 2 ^ 59
def prefixEnd_1811711 : Nat := 4983230072969 + 3 ^ 40 * 1811711 * 2
def baseEnd_1811711 : Nat := 930278550037866406080599

theorem tailTrace_1811711 : CollatzResearch.WordTrace tailWord_1811711 prefixEnd_1811711 930278550037866406080599 := by
  unfold tailWord_1811711
  simp only [CollatzResearch.WordTrace]
  refine ⟨66078528739487937450074987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44052352492991958300049991 66078528739487937450074987)
  ·
    refine ⟨99117793109231906175112481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66078528739487937450074987 99117793109231906175112481)
    ·
      refine ⟨74338344831923929631334361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99117793109231906175112481 74338344831923929631334361)
      ·
        refine ⟨55753758623942947223500771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74338344831923929631334361 55753758623942947223500771)
        ·
          refine ⟨83630637935914420835251157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55753758623942947223500771 83630637935914420835251157)
          ·
            refine ⟨1960093076622994238326199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83630637935914420835251157 1960093076622994238326199)
            ·
              refine ⟨2940139614934491357489299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960093076622994238326199 2940139614934491357489299)
              ·
                refine ⟨4410209422401737036233949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940139614934491357489299 4410209422401737036233949)
                ·
                  refine ⟨1653828533400651388587731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4410209422401737036233949 1653828533400651388587731)
                  ·
                    refine ⟨2480742800100977082881597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653828533400651388587731 2480742800100977082881597)
                    ·
                      refine ⟨930278550037866406080599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480742800100977082881597 930278550037866406080599)
                      ·
                        rfl

theorem cell23_1811711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_1811711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811711 prefixEnd_1811711 := by exact prefixLift 1811711
  have htrace : WordTrace (prefixWord ++ tailWord_1811711) baseStart_1811711 baseEnd_1811711 := by
    simpa [prefixWord, tailWord_1811711, baseEnd_1811711] using wordTrace_append hprefix tailTrace_1811711
  have hstable : (prefixWord ++ tailWord_1811711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811711).length < 2 ^ (prefixWord ++ tailWord_1811711).sum := by decide
  have hdescent : baseEnd_1811711 < baseStart_1811711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811717 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_1811717 : Nat := 118140960795 + 1811717 * 2 ^ 59
def prefixEnd_1811717 : Nat := 4983230072969 + 3 ^ 40 * 1811717 * 2
def baseEnd_1811717 : Nat := 930281630921793382605571

theorem tailTrace_1811717 : CollatzResearch.WordTrace tailWord_1811717 prefixEnd_1811717 930281630921793382605571 := by
  unfold tailWord_1811717
  simp only [CollatzResearch.WordTrace]
  refine ⟨66078747577466200474793405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44052498384977466983195603 66078747577466200474793405)
  ·
    refine ⟨24779530341549825178047527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66078747577466200474793405 24779530341549825178047527)
    ·
      refine ⟨37169295512324737767071291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24779530341549825178047527 37169295512324737767071291)
      ·
        refine ⟨55753943268487106650606937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37169295512324737767071291 55753943268487106650606937)
        ·
          refine ⟨41815457451365329987955203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55753943268487106650606937 41815457451365329987955203)
          ·
            refine ⟨62723186177047994981932805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41815457451365329987955203 62723186177047994981932805)
            ·
              refine ⟨11760597408196499059112401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62723186177047994981932805 11760597408196499059112401)
              ·
                refine ⟨8820448056147374294334301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11760597408196499059112401 8820448056147374294334301)
                ·
                  refine ⟨3307668021055265360375363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8820448056147374294334301 3307668021055265360375363)
                  ·
                    refine ⟨4961502031582898040563045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3307668021055265360375363 4961502031582898040563045)
                    ·
                      refine ⟨930281630921793382605571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4961502031582898040563045 930281630921793382605571)
                      ·
                        rfl

theorem cell23_1811717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_1811717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811717 prefixEnd_1811717 := by exact prefixLift 1811717
  have htrace : WordTrace (prefixWord ++ tailWord_1811717) baseStart_1811717 baseEnd_1811717 := by
    simpa [prefixWord, tailWord_1811717, baseEnd_1811717] using wordTrace_append hprefix tailTrace_1811717
  have hstable : (prefixWord ++ tailWord_1811717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811717).length < 2 ^ (prefixWord ++ tailWord_1811717).sum := by decide
  have hdescent : baseEnd_1811717 < baseStart_1811717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811744 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_1811744 : Nat := 118140960795 + 1811744 * 2 ^ 59
def prefixEnd_1811744 : Nat := 4983230072969 + 3 ^ 40 * 1811744 * 2
def baseEnd_1811744 : Nat := 310098498299821592322649

theorem tailTrace_1811744 : CollatzResearch.WordTrace tailWord_1811744 prefixEnd_1811744 310098498299821592322649 := by
  unfold tailWord_1811744
  simp only [CollatzResearch.WordTrace]
  refine ⟨33039866174184192043013143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44053154898912256057350857 33039866174184192043013143)
  ·
    refine ⟨49559799261276288064519715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33039866174184192043013143 49559799261276288064519715)
    ·
      refine ⟨74339698891914432096779573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49559799261276288064519715 74339698891914432096779573)
      ·
        refine ⟨6969346771116978009073085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74339698891914432096779573 6969346771116978009073085)
        ·
          refine ⟨2613505039168866753402407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6969346771116978009073085 2613505039168866753402407)
          ·
            refine ⟨3920257558753300130103611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613505039168866753402407 3920257558753300130103611)
            ·
              refine ⟨5880386338129950195155417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920257558753300130103611 5880386338129950195155417)
              ·
                refine ⟨4410289753597462646366563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880386338129950195155417 4410289753597462646366563)
                ·
                  refine ⟨6615434630396193969549845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410289753597462646366563 6615434630396193969549845)
                  ·
                    refine ⟨310098498299821592322649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6615434630396193969549845 310098498299821592322649)
                    ·
                      rfl

theorem cell23_1811744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_1811744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811744 prefixEnd_1811744 := by exact prefixLift 1811744
  have htrace : WordTrace (prefixWord ++ tailWord_1811744) baseStart_1811744 baseEnd_1811744 := by
    simpa [prefixWord, tailWord_1811744, baseEnd_1811744] using wordTrace_append hprefix tailTrace_1811744
  have hstable : (prefixWord ++ tailWord_1811744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811744).length < 2 ^ (prefixWord ++ tailWord_1811744).sum := by decide
  have hdescent : baseEnd_1811744 < baseStart_1811744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811747 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1811747 : Nat := 118140960795 + 1811747 * 2 ^ 59
def prefixEnd_1811747 : Nat := 4983230072969 + 3 ^ 40 * 1811747 * 2
def baseEnd_1811747 : Nat := 930297035341428265230433

theorem tailTrace_1811747 : CollatzResearch.WordTrace tailWord_1811747 prefixEnd_1811747 930297035341428265230433 := by
  unfold tailWord_1811747
  simp only [CollatzResearch.WordTrace]
  refine ⟨66079841767357515598385495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44053227844905010398923663 66079841767357515598385495)
  ·
    refine ⟨99119762651036273397578243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66079841767357515598385495 99119762651036273397578243)
    ·
      refine ⟨148679643976554410096367365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99119762651036273397578243 148679643976554410096367365)
      ·
        refine ⟨27877433245603951893068881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148679643976554410096367365 27877433245603951893068881)
        ·
          refine ⟨20908074934202963919801661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27877433245603951893068881 20908074934202963919801661)
          ·
            refine ⟨7840528100326111469925623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20908074934202963919801661 7840528100326111469925623)
            ·
              refine ⟨11760792150489167204888435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840528100326111469925623 11760792150489167204888435)
              ·
                refine ⟨17641188225733750807332653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11760792150489167204888435 17641188225733750807332653)
                ·
                  refine ⟨6615445584650156552749745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17641188225733750807332653 6615445584650156552749745)
                  ·
                    refine ⟨4961584188487617414562309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615445584650156552749745 4961584188487617414562309)
                    ·
                      refine ⟨930297035341428265230433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4961584188487617414562309 930297035341428265230433)
                      ·
                        rfl

theorem cell23_1811747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1811747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811747 prefixEnd_1811747 := by exact prefixLift 1811747
  have htrace : WordTrace (prefixWord ++ tailWord_1811747) baseStart_1811747 baseEnd_1811747 := by
    simpa [prefixWord, tailWord_1811747, baseEnd_1811747] using wordTrace_append hprefix tailTrace_1811747
  have hstable : (prefixWord ++ tailWord_1811747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811747).length < 2 ^ (prefixWord ++ tailWord_1811747).sum := by decide
  have hdescent : baseEnd_1811747 < baseStart_1811747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811761 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_1811761 : Nat := 118140960795 + 1811761 * 2 ^ 59
def prefixEnd_1811761 : Nat := 4983230072969 + 3 ^ 40 * 1811761 * 2
def baseEnd_1811761 : Nat := 310101408023530403485123

theorem tailTrace_1811761 : CollatzResearch.WordTrace tailWord_1811761 prefixEnd_1811761 310101408023530403485123 := by
  unfold tailWord_1811761
  simp only [CollatzResearch.WordTrace]
  refine ⟨66080352389306795989395137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44053568259537863992930091 66080352389306795989395137)
  ·
    refine ⟨49560264291980096992046353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66080352389306795989395137 49560264291980096992046353)
    ·
      refine ⟨37170198218985072744034765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49560264291980096992046353 37170198218985072744034765)
      ·
        refine ⟨13938824332119402279013037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37170198218985072744034765 13938824332119402279013037)
        ·
          refine ⟨5227059124544775854629889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13938824332119402279013037 5227059124544775854629889)
          ·
            refine ⟨3920294343408581890972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227059124544775854629889 3920294343408581890972417)
            ·
              refine ⟨2940220757556436418229313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3920294343408581890972417 2940220757556436418229313)
              ·
                refine ⟨2205165568167327313671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940220757556436418229313 2205165568167327313671985)
                ·
                  refine ⟨1653874176125495485253989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2205165568167327313671985 1653874176125495485253989)
                  ·
                    refine ⟨310101408023530403485123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1653874176125495485253989 310101408023530403485123)
                    ·
                      rfl

theorem cell23_1811761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_1811761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811761 prefixEnd_1811761 := by exact prefixLift 1811761
  have htrace : WordTrace (prefixWord ++ tailWord_1811761) baseStart_1811761 baseEnd_1811761 := by
    simpa [prefixWord, tailWord_1811761, baseEnd_1811761] using wordTrace_append hprefix tailTrace_1811761
  have hstable : (prefixWord ++ tailWord_1811761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811761).length < 2 ^ (prefixWord ++ tailWord_1811761).sum := by decide
  have hdescent : baseEnd_1811761 < baseStart_1811761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811764 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1811764 : Nat := 118140960795 + 1811764 * 2 ^ 59
def prefixEnd_1811764 : Nat := 4983230072969 + 3 ^ 40 * 1811764 * 2
def baseEnd_1811764 : Nat := 930305764512554698717855

theorem tailTrace_1811764 : CollatzResearch.WordTrace tailWord_1811764 prefixEnd_1811764 930305764512554698717855 := by
  unfold tailWord_1811764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040230904147963750877173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44053641205530618334502897 33040230904147963750877173)
  ·
    refine ⟨3097521647263871601644735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33040230904147963750877173 3097521647263871601644735)
    ·
      refine ⟨4646282470895807402467103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097521647263871601644735 4646282470895807402467103)
      ·
        refine ⟨6969423706343711103700655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646282470895807402467103 6969423706343711103700655)
        ·
          refine ⟨10454135559515566655550983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969423706343711103700655 10454135559515566655550983)
          ·
            refine ⟨15681203339273349983326475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454135559515566655550983 15681203339273349983326475)
            ·
              refine ⟨23521805008910024974989713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681203339273349983326475 23521805008910024974989713)
              ·
                refine ⟨17641353756682518731242285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23521805008910024974989713 17641353756682518731242285)
                ·
                  refine ⟨6615507658755944524215857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17641353756682518731242285 6615507658755944524215857)
                  ·
                    refine ⟨4961630744066958393161893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615507658755944524215857 4961630744066958393161893)
                    ·
                      refine ⟨930305764512554698717855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4961630744066958393161893 930305764512554698717855)
                      ·
                        rfl

theorem cell23_1811764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1811764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811764 prefixEnd_1811764 := by exact prefixLift 1811764
  have htrace : WordTrace (prefixWord ++ tailWord_1811764) baseStart_1811764 baseEnd_1811764 := by
    simpa [prefixWord, tailWord_1811764, baseEnd_1811764] using wordTrace_append hprefix tailTrace_1811764
  have hstable : (prefixWord ++ tailWord_1811764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811764).length < 2 ^ (prefixWord ++ tailWord_1811764).sum := by decide
  have hdescent : baseEnd_1811764 < baseStart_1811764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811784 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_1811784 : Nat := 118140960795 + 1811784 * 2 ^ 59
def prefixEnd_1811784 : Nat := 4983230072969 + 3 ^ 40 * 1811784 * 2
def baseEnd_1811784 : Nat := 930316034125644620467763

theorem tailTrace_1811784 : CollatzResearch.WordTrace tailWord_1811784 prefixEnd_1811784 930316034125644620467763 := by
  unfold tailWord_1811784
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040595634111735458741203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44054127512148980611654937 33040595634111735458741203)
  ·
    refine ⟨49560893451167603188111805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33040595634111735458741203 49560893451167603188111805)
    ·
      refine ⟨18585335044187851195541927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49560893451167603188111805 18585335044187851195541927)
      ·
        refine ⟨27878002566281776793312891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18585335044187851195541927 27878002566281776793312891)
        ·
          refine ⟨41817003849422665189969337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27878002566281776793312891 41817003849422665189969337)
          ·
            refine ⟨31362752887066998892477003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41817003849422665189969337 31362752887066998892477003)
            ·
              refine ⟨47044129330600498338715505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31362752887066998892477003 47044129330600498338715505)
              ·
                refine ⟨35283096997950373754036629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47044129330600498338715505 35283096997950373754036629)
                ·
                  refine ⟨1653895171778923769720467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35283096997950373754036629 1653895171778923769720467)
                  ·
                    refine ⟨2480842757668385654580701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653895171778923769720467 2480842757668385654580701)
                    ·
                      refine ⟨930316034125644620467763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480842757668385654580701 930316034125644620467763)
                      ·
                        rfl

theorem cell23_1811784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_1811784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811784 prefixEnd_1811784 := by exact prefixLift 1811784
  have htrace : WordTrace (prefixWord ++ tailWord_1811784) baseStart_1811784 baseEnd_1811784 := by
    simpa [prefixWord, tailWord_1811784, baseEnd_1811784] using wordTrace_append hprefix tailTrace_1811784
  have hstable : (prefixWord ++ tailWord_1811784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811784).length < 2 ^ (prefixWord ++ tailWord_1811784).sum := by decide
  have hdescent : baseEnd_1811784 < baseStart_1811784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811818 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1811818 : Nat := 118140960795 + 1811818 * 2 ^ 59
def prefixEnd_1811818 : Nat := 4983230072969 + 3 ^ 40 * 1811818 * 2
def baseEnd_1811818 : Nat := 930333492467897487442607

theorem tailTrace_1811818 : CollatzResearch.WordTrace tailWord_1811818 prefixEnd_1811818 930333492467897487442607 := by
  unfold tailWord_1811818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520607837525073681055027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44054954233400196482813405 16520607837525073681055027)
  ·
    refine ⟨24780911756287610521582541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16520607837525073681055027 24780911756287610521582541)
    ·
      refine ⟨9292841908607853945593453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24780911756287610521582541 9292841908607853945593453)
      ·
        refine ⟨3484815715727945229597545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9292841908607853945593453 3484815715727945229597545)
        ·
          refine ⟨2613611786795958922198159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484815715727945229597545 2613611786795958922198159)
          ·
            refine ⟨3920417680193938383297239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613611786795958922198159 3920417680193938383297239)
            ·
              refine ⟨5880626520290907574945859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920417680193938383297239 5880626520290907574945859)
              ·
                refine ⟨8820939780436361362418789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880626520290907574945859 8820939780436361362418789)
                ·
                  refine ⟨1653926208831817755453523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8820939780436361362418789 1653926208831817755453523)
                  ·
                    refine ⟨2480889313247726633180285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1653926208831817755453523 2480889313247726633180285)
                    ·
                      refine ⟨930333492467897487442607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2480889313247726633180285 930333492467897487442607)
                      ·
                        rfl

theorem cell23_1811818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1811818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811818 prefixEnd_1811818 := by exact prefixLift 1811818
  have htrace : WordTrace (prefixWord ++ tailWord_1811818) baseStart_1811818 baseEnd_1811818 := by
    simpa [prefixWord, tailWord_1811818, baseEnd_1811818] using wordTrace_append hprefix tailTrace_1811818
  have hstable : (prefixWord ++ tailWord_1811818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811818).length < 2 ^ (prefixWord ++ tailWord_1811818).sum := by decide
  have hdescent : baseEnd_1811818 < baseStart_1811818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811877 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_1811877 : Nat := 118140960795 + 1811877 * 2 ^ 59
def prefixEnd_1811877 : Nat := 4983230072969 + 3 ^ 40 * 1811877 * 2
def baseEnd_1811877 : Nat := 310121262608837585534945

theorem tailTrace_1811877 : CollatzResearch.WordTrace tailWord_1811877 prefixEnd_1811877 310121262608837585534945 := by
  unfold tailWord_1811877
  simp only [CollatzResearch.WordTrace]
  refine ⟨66084583256886547800617885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44056388837924365200411923 66084583256886547800617885)
  ·
    refine ⟨24781718721332455425231707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66084583256886547800617885 24781718721332455425231707)
    ·
      refine ⟨37172578081998683137847561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24781718721332455425231707 37172578081998683137847561)
      ·
        refine ⟨27879433561499012353385671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37172578081998683137847561 27879433561499012353385671)
        ·
          refine ⟨41819150342248518530078507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27879433561499012353385671 41819150342248518530078507)
          ·
            refine ⟨62728725513372777795117761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41819150342248518530078507 62728725513372777795117761)
            ·
              refine ⟨47046544135029583346338321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62728725513372777795117761 47046544135029583346338321)
              ·
                refine ⟨35284908101272187509753741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47046544135029583346338321 35284908101272187509753741)
                ·
                  refine ⟨13231840537977070316157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35284908101272187509753741 13231840537977070316157653)
                  ·
                    refine ⟨310121262608837585534945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13231840537977070316157653 310121262608837585534945)
                    ·
                      rfl

theorem cell23_1811877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_1811877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811877 prefixEnd_1811877 := by exact prefixLift 1811877
  have htrace : WordTrace (prefixWord ++ tailWord_1811877) baseStart_1811877 baseEnd_1811877 := by
    simpa [prefixWord, tailWord_1811877, baseEnd_1811877] using wordTrace_append hprefix tailTrace_1811877
  have hstable : (prefixWord ++ tailWord_1811877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811877).length < 2 ^ (prefixWord ++ tailWord_1811877).sum := by decide
  have hdescent : baseEnd_1811877 < baseStart_1811877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811907 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 8]
def baseStart_1811907 : Nat := 118140960795 + 1811907 * 2 ^ 59
def prefixEnd_1811907 : Nat := 4983230072969 + 3 ^ 40 * 1811907 * 2
def baseEnd_1811907 : Nat := 310126397415382546409899

theorem tailTrace_1811907 : CollatzResearch.WordTrace tailWord_1811907 prefixEnd_1811907 310126397415382546409899 := by
  unfold tailWord_1811907
  simp only [CollatzResearch.WordTrace]
  refine ⟨66085677446777862924209975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44057118297851908616139983 66085677446777862924209975)
  ·
    refine ⟨99128516170166794386314963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66085677446777862924209975 99128516170166794386314963)
    ·
      refine ⟨148692774255250191579472445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99128516170166794386314963 148692774255250191579472445)
      ·
        refine ⟨55759790345718821842302167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148692774255250191579472445 55759790345718821842302167)
        ·
          refine ⟨83639685518578232763453251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55759790345718821842302167 83639685518578232763453251)
          ·
            refine ⟨125459528277867349145179877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83639685518578232763453251 125459528277867349145179877)
            ·
              refine ⟨23523661552100127964721227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125459528277867349145179877 23523661552100127964721227)
              ·
                refine ⟨35285492328150191947081841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23523661552100127964721227 35285492328150191947081841)
                ·
                  refine ⟨26464119246112643960311381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35285492328150191947081841 26464119246112643960311381)
                  ·
                    refine ⟨310126397415382546409899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26464119246112643960311381 310126397415382546409899)
                    ·
                      rfl

theorem cell23_1811907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_1811907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811907 prefixEnd_1811907 := by exact prefixLift 1811907
  have htrace : WordTrace (prefixWord ++ tailWord_1811907) baseStart_1811907 baseEnd_1811907 := by
    simpa [prefixWord, tailWord_1811907, baseEnd_1811907] using wordTrace_append hprefix tailTrace_1811907
  have hstable : (prefixWord ++ tailWord_1811907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811907).length < 2 ^ (prefixWord ++ tailWord_1811907).sum := by decide
  have hdescent : baseEnd_1811907 < baseStart_1811907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811958 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1811958 : Nat := 118140960795 + 1811958 * 2 ^ 59
def prefixEnd_1811958 : Nat := 4983230072969 + 3 ^ 40 * 1811958 * 2
def baseEnd_1811958 : Nat := 310135126586508979897321

theorem tailTrace_1811958 : CollatzResearch.WordTrace tailWord_1811958 prefixEnd_1811958 310135126586508979897321 := by
  unfold tailWord_1811958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130471098099568664644783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44058358379728732422877685 4130471098099568664644783)
  ·
    refine ⟨6195706647149352996967175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4130471098099568664644783 6195706647149352996967175)
    ·
      refine ⟨9293559970724029495450763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6195706647149352996967175 9293559970724029495450763)
      ·
        refine ⟨13940339956086044243176145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9293559970724029495450763 13940339956086044243176145)
        ·
          refine ⟨10455254967064533182382109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13940339956086044243176145 10455254967064533182382109)
          ·
            refine ⟨3920720612649199943393291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10455254967064533182382109 3920720612649199943393291)
            ·
              refine ⟨5881080918973799915089937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920720612649199943393291 5881080918973799915089937)
              ·
                refine ⟨4410810689230349936317453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5881080918973799915089937 4410810689230349936317453)
                ·
                  refine ⟨1654054008461381226119045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4410810689230349936317453 1654054008461381226119045)
                  ·
                    refine ⟨310135126586508979897321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1654054008461381226119045 310135126586508979897321)
                    ·
                      rfl

theorem cell23_1811958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1811958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811958 prefixEnd_1811958 := by exact prefixLift 1811958
  have htrace : WordTrace (prefixWord ++ tailWord_1811958) baseStart_1811958 baseEnd_1811958 := by
    simpa [prefixWord, tailWord_1811958, baseEnd_1811958] using wordTrace_append hprefix tailTrace_1811958
  have hstable : (prefixWord ++ tailWord_1811958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811958).length < 2 ^ (prefixWord ++ tailWord_1811958).sum := by decide
  have hdescent : baseEnd_1811958 < baseStart_1811958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811975 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 1, 4]
def baseStart_1811975 : Nat := 118140960795 + 1811975 * 2 ^ 59
def prefixEnd_1811975 : Nat := 4983230072969 + 3 ^ 40 * 1811975 * 2
def baseEnd_1811975 : Nat := 310138036310217791059795

theorem tailTrace_1811975 : CollatzResearch.WordTrace tailWord_1811975 prefixEnd_1811975 310138036310217791059795 := by
  unfold tailWord_1811975
  simp only [CollatzResearch.WordTrace]
  refine ⟨66088157610531510537685379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44058771740354340358456919 66088157610531510537685379)
  ·
    refine ⟨99132236415797265806528069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66088157610531510537685379 99132236415797265806528069)
    ·
      refine ⟨18587294327961987338724013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99132236415797265806528069 18587294327961987338724013)
      ·
        refine ⟨6970235372985745252021505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18587294327961987338724013 6970235372985745252021505)
        ·
          refine ⟨5227676529739308939016129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970235372985745252021505 5227676529739308939016129)
          ·
            refine ⟨3920757397304481704262097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227676529739308939016129 3920757397304481704262097)
            ·
              refine ⟨2940568047978361278196573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3920757397304481704262097 2940568047978361278196573)
              ·
                refine ⟨1102713017991885479323715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2940568047978361278196573 1102713017991885479323715)
                ·
                  refine ⟨1654069526987828218985573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102713017991885479323715 1654069526987828218985573)
                  ·
                    refine ⟨310138036310217791059795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1654069526987828218985573 310138036310217791059795)
                    ·
                      rfl

theorem cell23_1811975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_1811975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811975 prefixEnd_1811975 := by exact prefixLift 1811975
  have htrace : WordTrace (prefixWord ++ tailWord_1811975) baseStart_1811975 baseEnd_1811975 := by
    simpa [prefixWord, tailWord_1811975, baseEnd_1811975] using wordTrace_append hprefix tailTrace_1811975
  have hstable : (prefixWord ++ tailWord_1811975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811975).length < 2 ^ (prefixWord ++ tailWord_1811975).sum := by decide
  have hdescent : baseEnd_1811975 < baseStart_1811975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1811988 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 8]
def baseStart_1811988 : Nat := 118140960795 + 1811988 * 2 ^ 59
def prefixEnd_1811988 : Nat := 4983230072969 + 3 ^ 40 * 1811988 * 2
def baseEnd_1811988 : Nat := 103380087131017980257425

theorem tailTrace_1811988 : CollatzResearch.WordTrace tailWord_1811988 prefixEnd_1811988 103380087131017980257425 := by
  unfold tailWord_1811988
  simp only [CollatzResearch.WordTrace]
  refine ⟨33044315879742206878954309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44059087839656275838605745 33044315879742206878954309)
  ·
    refine ⟨6195809227451663789803933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33044315879742206878954309 6195809227451663789803933)
    ·
      refine ⟨2323428460294373921176475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6195809227451663789803933 2323428460294373921176475)
      ·
        refine ⟨3485142690441560881764713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323428460294373921176475 3485142690441560881764713)
        ·
          refine ⟨2613857017831170661323535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485142690441560881764713 2613857017831170661323535)
          ·
            refine ⟨3920785526746755991985303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613857017831170661323535 3920785526746755991985303)
            ·
              refine ⟨5881178290120133987977955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920785526746755991985303 5881178290120133987977955)
              ·
                refine ⟨8821767435180200981966933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881178290120133987977955 8821767435180200981966933)
                ·
                  refine ⟨103380087131017980257425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8821767435180200981966933 103380087131017980257425)
                  ·
                    rfl

theorem cell23_1811988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_1811988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1811988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1811988 prefixEnd_1811988 := by exact prefixLift 1811988
  have htrace : WordTrace (prefixWord ++ tailWord_1811988) baseStart_1811988 baseEnd_1811988 := by
    simpa [prefixWord, tailWord_1811988, baseEnd_1811988] using wordTrace_append hprefix tailTrace_1811988
  have hstable : (prefixWord ++ tailWord_1811988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1811988).length < 2 ^ (prefixWord ++ tailWord_1811988).sum := by decide
  have hdescent : baseEnd_1811988 < baseStart_1811988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1811988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812031 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 4, 4]
def baseStart_1812031 : Nat := 118140960795 + 1812031 * 2 ^ 59
def prefixEnd_1812031 : Nat := 4983230072969 + 3 ^ 40 * 1812031 * 2
def baseEnd_1812031 : Nat := 310147621282435051359709

theorem tailTrace_1812031 : CollatzResearch.WordTrace tailWord_1812031 prefixEnd_1812031 310147621282435051359709 := by
  unfold tailWord_1812031
  simp only [CollatzResearch.WordTrace]
  refine ⟨66090200098328632101723947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44060133398885754734482631 66090200098328632101723947)
  ·
    refine ⟨99135300147492948152585921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66090200098328632101723947 99135300147492948152585921)
    ·
      refine ⟨74351475110619711114439441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99135300147492948152585921 74351475110619711114439441)
      ·
        refine ⟨55763606332964783335829581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74351475110619711114439441 55763606332964783335829581)
        ·
          refine ⟨20911352374861793750936093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55763606332964783335829581 20911352374861793750936093)
          ·
            refine ⟨7841757140573172656601035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20911352374861793750936093 7841757140573172656601035)
            ·
              refine ⟨11762635710859758984901553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841757140573172656601035 11762635710859758984901553)
              ·
                refine ⟨8821976783144819238676165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11762635710859758984901553 8821976783144819238676165)
                ·
                  refine ⟨1654120646839653607251781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8821976783144819238676165 1654120646839653607251781)
                  ·
                    refine ⟨310147621282435051359709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1654120646839653607251781 310147621282435051359709)
                    ·
                      rfl

theorem cell23_1812031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_1812031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812031 prefixEnd_1812031 := by exact prefixLift 1812031
  have htrace : WordTrace (prefixWord ++ tailWord_1812031) baseStart_1812031 baseEnd_1812031 := by
    simpa [prefixWord, tailWord_1812031, baseEnd_1812031] using wordTrace_append hprefix tailTrace_1812031
  have hstable : (prefixWord ++ tailWord_1812031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812031).length < 2 ^ (prefixWord ++ tailWord_1812031).sum := by decide
  have hdescent : baseEnd_1812031 < baseStart_1812031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812044 : List Nat := [2, 2, 1, 3, 1, 3, 11]
def baseStart_1812044 : Nat := 118140960795 + 1812044 * 2 ^ 59
def prefixEnd_1812044 : Nat := 4983230072969 + 3 ^ 40 * 1812044 * 2
def baseEnd_1812044 : Nat := 11487031346861896336007

theorem tailTrace_1812044 : CollatzResearch.WordTrace tailWord_1812044 prefixEnd_1812044 11487031346861896336007 := by
  unfold tailWord_1812044
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045337123640767660973593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44060449498187690214631457 33045337123640767660973593)
  ·
    refine ⟨24784002842730575745730195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33045337123640767660973593 24784002842730575745730195)
    ·
      refine ⟨37176004264095863618595293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24784002842730575745730195 37176004264095863618595293)
      ·
        refine ⟨13941001599035948856973235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37176004264095863618595293 13941001599035948856973235)
        ·
          refine ⟨20911502398553923285459853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13941001599035948856973235 20911502398553923285459853)
          ·
            refine ⟨7841813399457721232047445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20911502398553923285459853 7841813399457721232047445)
            ·
              refine ⟨11487031346861896336007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7841813399457721232047445 11487031346861896336007)
              ·
                rfl

theorem cell23_1812044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 11].length) (baseStart_1812044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812044 prefixEnd_1812044 := by exact prefixLift 1812044
  have htrace : WordTrace (prefixWord ++ tailWord_1812044) baseStart_1812044 baseEnd_1812044 := by
    simpa [prefixWord, tailWord_1812044, baseEnd_1812044] using wordTrace_append hprefix tailTrace_1812044
  have hstable : (prefixWord ++ tailWord_1812044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812044).length < 2 ^ (prefixWord ++ tailWord_1812044).sum := by decide
  have hdescent : baseEnd_1812044 < baseStart_1812044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812055 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_1812055 : Nat := 118140960795 + 1812055 * 2 ^ 59
def prefixEnd_1812055 : Nat := 4983230072969 + 3 ^ 40 * 1812055 * 2
def baseEnd_1812055 : Nat := 930455187383013060179017

theorem tailTrace_1812055 : CollatzResearch.WordTrace tailWord_1812055 prefixEnd_1812055 930455187383013060179017 := by
  unfold tailWord_1812055
  simp only [CollatzResearch.WordTrace]
  refine ⟨66091075450241684200597619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44060716966827789467065079 66091075450241684200597619)
  ·
    refine ⟨99136613175362526300896429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66091075450241684200597619 99136613175362526300896429)
    ·
      refine ⟨37176229940760947362836161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99136613175362526300896429 37176229940760947362836161)
      ·
        refine ⟨27882172455570710522127121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37176229940760947362836161 27882172455570710522127121)
        ·
          refine ⟨20911629341678032891595341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27882172455570710522127121 20911629341678032891595341)
          ·
            refine ⟨7841861003129262334348253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20911629341678032891595341 7841861003129262334348253)
            ·
              refine ⟨2940697876173473375380595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7841861003129262334348253 2940697876173473375380595)
              ·
                refine ⟨4411046814260210063070893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940697876173473375380595 4411046814260210063070893)
                ·
                  refine ⟨1654142555347578773651585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4411046814260210063070893 1654142555347578773651585)
                  ·
                    refine ⟨1240606916510684080238689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654142555347578773651585 1240606916510684080238689)
                    ·
                      refine ⟨930455187383013060179017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240606916510684080238689 930455187383013060179017)
                      ·
                        rfl

theorem cell23_1812055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_1812055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812055 prefixEnd_1812055 := by exact prefixLift 1812055
  have htrace : WordTrace (prefixWord ++ tailWord_1812055) baseStart_1812055 baseEnd_1812055 := by
    simpa [prefixWord, tailWord_1812055, baseEnd_1812055] using wordTrace_append hprefix tailTrace_1812055
  have hstable : (prefixWord ++ tailWord_1812055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812055).length < 2 ^ (prefixWord ++ tailWord_1812055).sum := by decide
  have hdescent : baseEnd_1812055 < baseStart_1812055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812064 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1812064 : Nat := 118140960795 + 1812064 * 2 ^ 59
def prefixEnd_1812064 : Nat := 4983230072969 + 3 ^ 40 * 1812064 * 2
def baseEnd_1812064 : Nat := 930459808708903524966475

theorem tailTrace_1812064 : CollatzResearch.WordTrace tailWord_1812064 prefixEnd_1812064 930459808708903524966475 := by
  unfold tailWord_1812064
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045701853604539368837623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44060935804806052491783497 33045701853604539368837623)
  ·
    refine ⟨49568552780406809053256435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33045701853604539368837623 49568552780406809053256435)
    ·
      refine ⟨74352829170610213579884653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49568552780406809053256435 74352829170610213579884653)
      ·
        refine ⟨27882310938978830092456745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74352829170610213579884653 27882310938978830092456745)
        ·
          refine ⟨20911733204234122569342559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27882310938978830092456745 20911733204234122569342559)
          ·
            refine ⟨31367599806351183854013839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20911733204234122569342559 31367599806351183854013839)
            ·
              refine ⟨47051399709526775781020759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31367599806351183854013839 47051399709526775781020759)
              ·
                refine ⟨70577099564290163671531139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47051399709526775781020759 70577099564290163671531139)
                ·
                  refine ⟨105865649346435245507296709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70577099564290163671531139 105865649346435245507296709)
                  ·
                    refine ⟨19849809252456608532618133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105865649346435245507296709 19849809252456608532618133)
                    ·
                      refine ⟨930459808708903524966475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19849809252456608532618133 930459808708903524966475)
                      ·
                        rfl

theorem cell23_1812064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1812064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812064 prefixEnd_1812064 := by exact prefixLift 1812064
  have htrace : WordTrace (prefixWord ++ tailWord_1812064) baseStart_1812064 baseEnd_1812064 := by
    simpa [prefixWord, tailWord_1812064, baseEnd_1812064] using wordTrace_append hprefix tailTrace_1812064
  have hstable : (prefixWord ++ tailWord_1812064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812064).length < 2 ^ (prefixWord ++ tailWord_1812064).sum := by decide
  have hdescent : baseEnd_1812064 < baseStart_1812064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812106 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_1812106 : Nat := 118140960795 + 1812106 * 2 ^ 59
def prefixEnd_1812106 : Nat := 4983230072969 + 3 ^ 40 * 1812106 * 2
def baseEnd_1812106 : Nat := 930481374896392360641283

theorem tailTrace_1812106 : CollatzResearch.WordTrace tailWord_1812106 prefixEnd_1812106 930481374896392360641283 := by
  unfold tailWord_1812106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16523233893264229977676043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44061957048704613273802781 16523233893264229977676043)
  ·
    refine ⟨24784850839896344966514065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16523233893264229977676043 24784850839896344966514065)
    ·
      refine ⟨18588638129922258724885549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24784850839896344966514065 18588638129922258724885549)
      ·
        refine ⟨6970739298720847021832081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18588638129922258724885549 6970739298720847021832081)
        ·
          refine ⟨5228054474040635266374061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970739298720847021832081 5228054474040635266374061)
          ·
            refine ⟨1960520427765238224890273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5228054474040635266374061 1960520427765238224890273)
            ·
              refine ⟨1470390320823928668667705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960520427765238224890273 1470390320823928668667705)
              ·
                refine ⟨1102792740617946501500779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470390320823928668667705 1102792740617946501500779)
                ·
                  refine ⟨1654189110926919752251169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102792740617946501500779 1654189110926919752251169)
                  ·
                    refine ⟨1240641833195189814188377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654189110926919752251169 1240641833195189814188377)
                    ·
                      refine ⟨930481374896392360641283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240641833195189814188377 930481374896392360641283)
                      ·
                        rfl

theorem cell23_1812106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_1812106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812106 prefixEnd_1812106 := by exact prefixLift 1812106
  have htrace : WordTrace (prefixWord ++ tailWord_1812106) baseStart_1812106 baseEnd_1812106 := by
    simpa [prefixWord, tailWord_1812106, baseEnd_1812106] using wordTrace_append hprefix tailTrace_1812106
  have hstable : (prefixWord ++ tailWord_1812106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812106).length < 2 ^ (prefixWord ++ tailWord_1812106).sum := by decide
  have hdescent : baseEnd_1812106 < baseStart_1812106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812131 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1812131 : Nat := 118140960795 + 1812131 * 2 ^ 59
def prefixEnd_1812131 : Nat := 4983230072969 + 3 ^ 40 * 1812131 * 2
def baseEnd_1812131 : Nat := 930494211912754762828667

theorem tailTrace_1812131 : CollatzResearch.WordTrace tailWord_1812131 prefixEnd_1812131 930494211912754762828667 := by
  unfold tailWord_1812131
  simp only [CollatzResearch.WordTrace]
  refine ⟨66093847397966349180364247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44062564931977566120242831 66093847397966349180364247)
  ·
    refine ⟨99140771096949523770546371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66093847397966349180364247 99140771096949523770546371)
    ·
      refine ⟨148711156645424285655819557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99140771096949523770546371 148711156645424285655819557)
      ·
        refine ⟨27883341871017053560466167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148711156645424285655819557 27883341871017053560466167)
        ·
          refine ⟨41825012806525580340699251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27883341871017053560466167 41825012806525580340699251)
          ·
            refine ⟨62737519209788370511048877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41825012806525580340699251 62737519209788370511048877)
            ·
              refine ⟨23526569703670638941643329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62737519209788370511048877 23526569703670638941643329)
              ·
                refine ⟨17644927277752979206232497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23526569703670638941643329 17644927277752979206232497)
                ·
                  refine ⟨13233695458314734404674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17644927277752979206232497 13233695458314734404674373)
                  ·
                    refine ⟨2481317898434012700876445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13233695458314734404674373 2481317898434012700876445)
                    ·
                      refine ⟨930494211912754762828667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2481317898434012700876445 930494211912754762828667)
                      ·
                        rfl

theorem cell23_1812131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1812131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812131 prefixEnd_1812131 := by exact prefixLift 1812131
  have htrace : WordTrace (prefixWord ++ tailWord_1812131) baseStart_1812131 baseEnd_1812131 := by
    simpa [prefixWord, tailWord_1812131, baseEnd_1812131] using wordTrace_append hprefix tailTrace_1812131
  have hstable : (prefixWord ++ tailWord_1812131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812131).length < 2 ^ (prefixWord ++ tailWord_1812131).sum := by decide
  have hdescent : baseEnd_1812131 < baseStart_1812131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812158 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1812158 : Nat := 118140960795 + 1812158 * 2 ^ 59
def prefixEnd_1812158 : Nat := 4983230072969 + 3 ^ 40 * 1812158 * 2
def baseEnd_1812158 : Nat := 930508075890426157191043

theorem tailTrace_1812158 : CollatzResearch.WordTrace tailWord_1812158 prefixEnd_1812158 930508075890426157191043 := by
  unfold tailWord_1812158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261854021108566598949641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44063221445912355194398085 8261854021108566598949641)
  ·
    refine ⟨6196390515831424949212231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8261854021108566598949641 6196390515831424949212231)
    ·
      refine ⟨9294585773747137423818347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6196390515831424949212231 9294585773747137423818347)
      ·
        refine ⟨13941878660620706135727521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9294585773747137423818347 13941878660620706135727521)
        ·
          refine ⟨10456408995465529601795641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13941878660620706135727521 10456408995465529601795641)
          ·
            refine ⟨7842306746599147201346731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10456408995465529601795641 7842306746599147201346731)
            ·
              refine ⟨11763460119898720802020097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842306746599147201346731 11763460119898720802020097)
              ·
                refine ⟨8822595089924040601515073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763460119898720802020097 8822595089924040601515073)
                ·
                  refine ⟨6616946317443030451136305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822595089924040601515073 6616946317443030451136305)
                  ·
                    refine ⟨4962709738082272838352229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616946317443030451136305 4962709738082272838352229)
                    ·
                      refine ⟨930508075890426157191043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4962709738082272838352229 930508075890426157191043)
                      ·
                        rfl

theorem cell23_1812158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1812158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812158 prefixEnd_1812158 := by exact prefixLift 1812158
  have htrace : WordTrace (prefixWord ++ tailWord_1812158) baseStart_1812158 baseEnd_1812158 := by
    simpa [prefixWord, tailWord_1812158, baseEnd_1812158] using wordTrace_append hprefix tailTrace_1812158
  have hstable : (prefixWord ++ tailWord_1812158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812158).length < 2 ^ (prefixWord ++ tailWord_1812158).sum := by decide
  have hdescent : baseEnd_1812158 < baseStart_1812158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812168 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 5]
def baseStart_1812168 : Nat := 118140960795 + 1812168 * 2 ^ 59
def prefixEnd_1812168 : Nat := 4983230072969 + 3 ^ 40 * 1812168 * 2
def baseEnd_1812168 : Nat := 103390356744107902007333

theorem tailTrace_1812168 : CollatzResearch.WordTrace tailWord_1812168 prefixEnd_1812168 103390356744107902007333 := by
  unfold tailWord_1812168
  simp only [CollatzResearch.WordTrace]
  refine ⟨33047598449416152249730579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44063464599221536332974105 33047598449416152249730579)
  ·
    refine ⟨49571397674124228374595869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33047598449416152249730579 49571397674124228374595869)
    ·
      refine ⟨18589274127796585640473451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49571397674124228374595869 18589274127796585640473451)
      ·
        refine ⟨27883911191694878460710177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18589274127796585640473451 27883911191694878460710177)
        ·
          refine ⟨20912933393771158845532633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27883911191694878460710177 20912933393771158845532633)
          ·
            refine ⟨15684700045328369134149475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20912933393771158845532633 15684700045328369134149475)
            ·
              refine ⟨23527050067992553701224213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15684700045328369134149475 23527050067992553701224213)
              ·
                refine ⟨1102830471937150954744885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23527050067992553701224213 1102830471937150954744885)
                ·
                  refine ⟨103390356744107902007333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1102830471937150954744885 103390356744107902007333)
                  ·
                    rfl

theorem cell23_1812168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 5].length) (baseStart_1812168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812168 prefixEnd_1812168 := by exact prefixLift 1812168
  have htrace : WordTrace (prefixWord ++ tailWord_1812168) baseStart_1812168 baseEnd_1812168 := by
    simpa [prefixWord, tailWord_1812168, baseEnd_1812168] using wordTrace_append hprefix tailTrace_1812168
  have hstable : (prefixWord ++ tailWord_1812168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812168).length < 2 ^ (prefixWord ++ tailWord_1812168).sum := by decide
  have hdescent : baseEnd_1812168 < baseStart_1812168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812221 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1812221 : Nat := 118140960795 + 1812221 * 2 ^ 59
def prefixEnd_1812221 : Nat := 4983230072969 + 3 ^ 40 * 1812221 * 2
def baseEnd_1812221 : Nat := 930540425171659410703253

theorem tailTrace_1812221 : CollatzResearch.WordTrace tailWord_1812221 prefixEnd_1812221 930540425171659410703253 := by
  unfold tailWord_1812221
  simp only [CollatzResearch.WordTrace]
  refine ⟨66097129967640294551140517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44064753311760196367427011 66097129967640294551140517)
  ·
    refine ⟨12393211868932555228338847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66097129967640294551140517 12393211868932555228338847)
    ·
      refine ⟨18589817803398832842508271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393211868932555228338847 18589817803398832842508271)
      ·
        refine ⟨27884726705098249263762407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18589817803398832842508271 27884726705098249263762407)
        ·
          refine ⟨41827090057647373895643611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27884726705098249263762407 41827090057647373895643611)
          ·
            refine ⟨62740635086471060843465417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41827090057647373895643611 62740635086471060843465417)
            ·
              refine ⟨47055476314853295632599063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62740635086471060843465417 47055476314853295632599063)
              ·
                refine ⟨70583214472279943448898595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47055476314853295632599063 70583214472279943448898595)
                ·
                  refine ⟨105874821708419915173347893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70583214472279943448898595 105874821708419915173347893)
                  ·
                    refine ⟨9925764535164367047501365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105874821708419915173347893 9925764535164367047501365)
                    ·
                      refine ⟨930540425171659410703253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9925764535164367047501365 930540425171659410703253)
                      ·
                        rfl

theorem cell23_1812221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1812221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812221 prefixEnd_1812221 := by exact prefixLift 1812221
  have htrace : WordTrace (prefixWord ++ tailWord_1812221) baseStart_1812221 baseEnd_1812221 := by
    simpa [prefixWord, tailWord_1812221, baseEnd_1812221] using wordTrace_append hprefix tailTrace_1812221
  have hstable : (prefixWord ++ tailWord_1812221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812221).length < 2 ^ (prefixWord ++ tailWord_1812221).sum := by decide
  have hdescent : baseEnd_1812221 < baseStart_1812221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812238 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1812238 : Nat := 118140960795 + 1812238 * 2 ^ 59
def prefixEnd_1812238 : Nat := 4983230072969 + 3 ^ 40 * 1812238 * 2
def baseEnd_1812238 : Nat := 930549154342785844190675

theorem tailTrace_1812238 : CollatzResearch.WordTrace tailWord_1812238 prefixEnd_1812238 930549154342785844190675 := by
  unfold tailWord_1812238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262218751072338306813671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44065166672385804303006245 8262218751072338306813671)
  ·
    refine ⟨12393328126608507460220507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8262218751072338306813671 12393328126608507460220507)
    ·
      refine ⟨18589992189912761190330761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393328126608507460220507 18589992189912761190330761)
      ·
        refine ⟨13942494142434570892748071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18589992189912761190330761 13942494142434570892748071)
        ·
          refine ⟨20913741213651856339122107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942494142434570892748071 20913741213651856339122107)
          ·
            refine ⟨31370611820477784508683161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20913741213651856339122107 31370611820477784508683161)
            ·
              refine ⟨23527958865358338381512371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31370611820477784508683161 23527958865358338381512371)
              ·
                refine ⟨35291938298037507572268557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23527958865358338381512371 35291938298037507572268557)
                ·
                  refine ⟨13234476861764065339600709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35291938298037507572268557 13234476861764065339600709)
                  ·
                    refine ⟨2481464411580762251175133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13234476861764065339600709 2481464411580762251175133)
                    ·
                      refine ⟨930549154342785844190675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2481464411580762251175133 930549154342785844190675)
                      ·
                        rfl

theorem cell23_1812238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1812238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812238 prefixEnd_1812238 := by exact prefixLift 1812238
  have htrace : WordTrace (prefixWord ++ tailWord_1812238) baseStart_1812238 baseEnd_1812238 := by
    simpa [prefixWord, tailWord_1812238, baseEnd_1812238] using wordTrace_append hprefix tailTrace_1812238
  have hstable : (prefixWord ++ tailWord_1812238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812238).length < 2 ^ (prefixWord ++ tailWord_1812238).sum := by decide
  have hdescent : baseEnd_1812238 < baseStart_1812238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812255 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1812255 : Nat := 118140960795 + 1812255 * 2 ^ 59
def prefixEnd_1812255 : Nat := 4983230072969 + 3 ^ 40 * 1812255 * 2
def baseEnd_1812255 : Nat := 930557883513912277678097

theorem tailTrace_1812255 : CollatzResearch.WordTrace tailWord_1812255 prefixEnd_1812255 930557883513912277678097 := by
  unfold tailWord_1812255
  simp only [CollatzResearch.WordTrace]
  refine ⟨66098370049517118357878219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44065580033011412238585479 66098370049517118357878219)
  ·
    refine ⟨99147555074275677536817329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66098370049517118357878219 99147555074275677536817329)
    ·
      refine ⟨74360666305706758152612997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99147555074275677536817329 74360666305706758152612997)
      ·
        refine ⟨13942624932320017153614937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74360666305706758152612997 13942624932320017153614937)
        ·
          refine ⟨10456968699240012865211203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13942624932320017153614937 10456968699240012865211203)
          ·
            refine ⟨15685453048860019297816805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10456968699240012865211203 15685453048860019297816805)
            ·
              refine ⟨2941022446661253618340651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15685453048860019297816805 2941022446661253618340651)
              ·
                refine ⟨4411533669991880427510977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941022446661253618340651 4411533669991880427510977)
                ·
                  refine ⟨3308650252493910320633233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411533669991880427510977 3308650252493910320633233)
                  ·
                    refine ⟨2481487689370432740474925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308650252493910320633233 2481487689370432740474925)
                    ·
                      refine ⟨930557883513912277678097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2481487689370432740474925 930557883513912277678097)
                      ·
                        rfl

theorem cell23_1812255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1812255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812255 prefixEnd_1812255 := by exact prefixLift 1812255
  have htrace : WordTrace (prefixWord ++ tailWord_1812255) baseStart_1812255 baseEnd_1812255 := by
    simpa [prefixWord, tailWord_1812255, baseEnd_1812255] using wordTrace_append hprefix tailTrace_1812255
  have hstable : (prefixWord ++ tailWord_1812255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812255).length < 2 ^ (prefixWord ++ tailWord_1812255).sum := by decide
  have hdescent : baseEnd_1812255 < baseStart_1812255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812275 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 6]
def baseStart_1812275 : Nat := 118140960795 + 1812275 * 2 ^ 59
def prefixEnd_1812275 : Nat := 4983230072969 + 3 ^ 40 * 1812275 * 2
def baseEnd_1812275 : Nat := 103396461458555799936445

theorem tailTrace_1812275 : CollatzResearch.WordTrace tailWord_1812275 prefixEnd_1812275 103396461458555799936445 := by
  unfold tailWord_1812275
  simp only [CollatzResearch.WordTrace]
  refine ⟨66099099509444661773606279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44066066339629774515737519 66099099509444661773606279)
  ·
    refine ⟨99148649264166992660409419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66099099509444661773606279 99148649264166992660409419)
    ·
      refine ⟨148722973896250488990614129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99148649264166992660409419 148722973896250488990614129)
      ·
        refine ⟨111542230422187866742960597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148722973896250488990614129 111542230422187866742960597)
        ·
          refine ⟨2614271025520028126788139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 111542230422187866742960597 2614271025520028126788139)
          ·
            refine ⟨3921406538280042190182209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614271025520028126788139 3921406538280042190182209)
            ·
              refine ⟨2941054903710031642636657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921406538280042190182209 2941054903710031642636657)
              ·
                refine ⟨2205791177782523731977493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941054903710031642636657 2205791177782523731977493)
                ·
                  refine ⟨103396461458555799936445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2205791177782523731977493 103396461458555799936445)
                  ·
                    rfl

theorem cell23_1812275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 6].length) (baseStart_1812275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812275 prefixEnd_1812275 := by exact prefixLift 1812275
  have htrace : WordTrace (prefixWord ++ tailWord_1812275) baseStart_1812275 baseEnd_1812275 := by
    simpa [prefixWord, tailWord_1812275, baseEnd_1812275] using wordTrace_append hprefix tailTrace_1812275
  have hstable : (prefixWord ++ tailWord_1812275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812275).length < 2 ^ (prefixWord ++ tailWord_1812275).sum := by decide
  have hdescent : baseEnd_1812275 < baseStart_1812275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812295 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_1812295 : Nat := 118140960795 + 1812295 * 2 ^ 59
def prefixEnd_1812295 : Nat := 4983230072969 + 3 ^ 40 * 1812295 * 2
def baseEnd_1812295 : Nat := 930578422740092121177913

theorem tailTrace_1812295 : CollatzResearch.WordTrace tailWord_1812295 prefixEnd_1812295 930578422740092121177913 := by
  unfold tailWord_1812295
  simp only [CollatzResearch.WordTrace]
  refine ⟨66099828969372205189334339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44066552646248136792889559 66099828969372205189334339)
  ·
    refine ⟨99149743454058307784001509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66099828969372205189334339 99149743454058307784001509)
    ·
      refine ⟨18590576897635932709500283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99149743454058307784001509 18590576897635932709500283)
      ·
        refine ⟨27885865346453899064250425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18590576897635932709500283 27885865346453899064250425)
        ·
          refine ⟨20914399009840424298187819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27885865346453899064250425 20914399009840424298187819)
          ·
            refine ⟨31371598514760636447281729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20914399009840424298187819 31371598514760636447281729)
            ·
              refine ⟨23528698886070477335461297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31371598514760636447281729 23528698886070477335461297)
              ·
                refine ⟨17646524164552858001595973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23528698886070477335461297 17646524164552858001595973)
                ·
                  refine ⟨3308723280853660875299245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17646524164552858001595973 3308723280853660875299245)
                  ·
                    refine ⟨1240771230320122828237217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308723280853660875299245 1240771230320122828237217)
                    ·
                      refine ⟨930578422740092121177913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240771230320122828237217 930578422740092121177913)
                      ·
                        rfl

theorem cell23_1812295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_1812295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812295 prefixEnd_1812295 := by exact prefixLift 1812295
  have htrace : WordTrace (prefixWord ++ tailWord_1812295) baseStart_1812295 baseEnd_1812295 := by
    simpa [prefixWord, tailWord_1812295, baseEnd_1812295] using wordTrace_append hprefix tailTrace_1812295
  have hstable : (prefixWord ++ tailWord_1812295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812295).length < 2 ^ (prefixWord ++ tailWord_1812295).sum := by decide
  have hdescent : baseEnd_1812295 < baseStart_1812295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812319 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 1, 1, 3]
def baseStart_1812319 : Nat := 118140960795 + 1812319 * 2 ^ 59
def prefixEnd_1812319 : Nat := 4983230072969 + 3 ^ 40 * 1812319 * 2
def baseEnd_1812319 : Nat := 930590746275800027277803

theorem tailTrace_1812319 : CollatzResearch.WordTrace tailWord_1812319 prefixEnd_1812319 930590746275800027277803 := by
  unfold tailWord_1812319
  simp only [CollatzResearch.WordTrace]
  refine ⟨66100704321285257288208011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44067136214190171525472007 66100704321285257288208011)
  ·
    refine ⟨99151056481927885932312017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66100704321285257288208011 99151056481927885932312017)
    ·
      refine ⟨74363292361445914449234013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99151056481927885932312017 74363292361445914449234013)
      ·
        refine ⟨27886234635542217918462755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74363292361445914449234013 27886234635542217918462755)
        ·
          refine ⟨41829351953313326877694133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27886234635542217918462755 41829351953313326877694133)
          ·
            refine ⟨3921501745623124394783825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41829351953313326877694133 3921501745623124394783825)
            ·
              refine ⟨2941126309217343296087869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921501745623124394783825 2941126309217343296087869)
              ·
                refine ⟨1102922365956503736032951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2941126309217343296087869 1102922365956503736032951)
                ·
                  refine ⟨1654383548934755604049427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102922365956503736032951 1654383548934755604049427)
                  ·
                    refine ⟨2481575323402133406074141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1654383548934755604049427 2481575323402133406074141)
                    ·
                      refine ⟨930590746275800027277803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2481575323402133406074141 930590746275800027277803)
                      ·
                        rfl

theorem cell23_1812319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_1812319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812319 prefixEnd_1812319 := by exact prefixLift 1812319
  have htrace : WordTrace (prefixWord ++ tailWord_1812319) baseStart_1812319 baseEnd_1812319 := by
    simpa [prefixWord, tailWord_1812319, baseEnd_1812319] using wordTrace_append hprefix tailTrace_1812319
  have hstable : (prefixWord ++ tailWord_1812319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812319).length < 2 ^ (prefixWord ++ tailWord_1812319).sum := by decide
  have hdescent : baseEnd_1812319 < baseStart_1812319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812322 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1812322 : Nat := 118140960795 + 1812322 * 2 ^ 59
def prefixEnd_1812322 : Nat := 4983230072969 + 3 ^ 40 * 1812322 * 2
def baseEnd_1812322 : Nat := 310197428905921171846763

theorem tailTrace_1812322 : CollatzResearch.WordTrace tailWord_1812322 prefixEnd_1812322 310197428905921171846763 := by
  unfold tailWord_1812322
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525203435068597200141805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44067209160182925867044813 16525203435068597200141805)
  ·
    refine ⟨6196951288150723950053177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16525203435068597200141805 6196951288150723950053177)
    ·
      refine ⟨4647713466113042962539883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6196951288150723950053177 4647713466113042962539883)
      ·
        refine ⟨6971570199169564443809825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647713466113042962539883 6971570199169564443809825)
        ·
          refine ⟨5228677649377173332857369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6971570199169564443809825 5228677649377173332857369)
          ·
            refine ⟨3921508237032879999643027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5228677649377173332857369 3921508237032879999643027)
            ·
              refine ⟨5882262355549319999464541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921508237032879999643027 5882262355549319999464541)
              ·
                refine ⟨2205848383330994999799203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5882262355549319999464541 2205848383330994999799203)
                ·
                  refine ⟨3308772574996492499698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205848383330994999799203 3308772574996492499698805)
                  ·
                    refine ⟨310197428905921171846763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3308772574996492499698805 310197428905921171846763)
                    ·
                      rfl

theorem cell23_1812322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1812322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812322 prefixEnd_1812322 := by exact prefixLift 1812322
  have htrace : WordTrace (prefixWord ++ tailWord_1812322) baseStart_1812322 baseEnd_1812322 := by
    simpa [prefixWord, tailWord_1812322, baseEnd_1812322] using wordTrace_append hprefix tailTrace_1812322
  have hstable : (prefixWord ++ tailWord_1812322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812322).length < 2 ^ (prefixWord ++ tailWord_1812322).sum := by decide
  have hdescent : baseEnd_1812322 < baseStart_1812322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812338 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1812338 : Nat := 118140960795 + 1812338 * 2 ^ 59
def prefixEnd_1812338 : Nat := 4983230072969 + 3 ^ 40 * 1812338 * 2
def baseEnd_1812338 : Nat := 930600502408235452940215

theorem tailTrace_1812338 : CollatzResearch.WordTrace tailWord_1812338 prefixEnd_1812338 930600502408235452940215 := by
  unfold tailWord_1812338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525349327054105883287417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44067598205477615688766445 16525349327054105883287417)
  ·
    refine ⟨12394011995290579412465563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16525349327054105883287417 12394011995290579412465563)
    ·
      refine ⟨18591017992935869118698345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12394011995290579412465563 18591017992935869118698345)
      ·
        refine ⟨13943263494701901839023759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18591017992935869118698345 13943263494701901839023759)
        ·
          refine ⟨20914895242052852758535639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13943263494701901839023759 20914895242052852758535639)
          ·
            refine ⟨31372342863079279137803459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20914895242052852758535639 31372342863079279137803459)
            ·
              refine ⟨47058514294618918706705189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31372342863079279137803459 47058514294618918706705189)
              ·
                refine ⟨8823471430241047257507223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47058514294618918706705189 8823471430241047257507223)
                ·
                  refine ⟨13235207145361570886260835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823471430241047257507223 13235207145361570886260835)
                  ·
                    refine ⟨19852810718042356329391253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13235207145361570886260835 19852810718042356329391253)
                    ·
                      refine ⟨930600502408235452940215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19852810718042356329391253 930600502408235452940215)
                      ·
                        rfl

theorem cell23_1812338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1812338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812338 prefixEnd_1812338 := by exact prefixLift 1812338
  have htrace : WordTrace (prefixWord ++ tailWord_1812338) baseStart_1812338 baseEnd_1812338 := by
    simpa [prefixWord, tailWord_1812338, baseEnd_1812338] using wordTrace_append hprefix tailTrace_1812338
  have hstable : (prefixWord ++ tailWord_1812338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812338).length < 2 ^ (prefixWord ++ tailWord_1812338).sum := by decide
  have hdescent : baseEnd_1812338 < baseStart_1812338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812352 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 2, 4]
def baseStart_1812352 : Nat := 118140960795 + 1812352 * 2 ^ 59
def prefixEnd_1812352 : Nat := 4983230072969 + 3 ^ 40 * 1812352 * 2
def baseEnd_1812352 : Nat := 310202563712466132721717

theorem tailTrace_1812352 : CollatzResearch.WordTrace tailWord_1812352 prefixEnd_1812352 310202563712466132721717 := by
  unfold tailWord_1812352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33050953965082851962079655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44067938620110469282772873 33050953965082851962079655)
  ·
    refine ⟨49576430947624277943119483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33050953965082851962079655 49576430947624277943119483)
    ·
      refine ⟨74364646421436416914679225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49576430947624277943119483 74364646421436416914679225)
      ·
        refine ⟨55773484816077312686009419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74364646421436416914679225 55773484816077312686009419)
        ·
          refine ⟨83660227224115969029014129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55773484816077312686009419 83660227224115969029014129)
          ·
            refine ⟨62745170418086976771760597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83660227224115969029014129 62745170418086976771760597)
            ·
              refine ⟨1470589931673913518088139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62745170418086976771760597 1470589931673913518088139)
              ·
                refine ⟨2205884897510870277132209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470589931673913518088139 2205884897510870277132209)
                ·
                  refine ⟨1654413673133152707849157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2205884897510870277132209 1654413673133152707849157)
                  ·
                    refine ⟨310202563712466132721717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1654413673133152707849157 310202563712466132721717)
                    ·
                      rfl

theorem cell23_1812352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_1812352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812352 prefixEnd_1812352 := by exact prefixLift 1812352
  have htrace : WordTrace (prefixWord ++ tailWord_1812352) baseStart_1812352 baseEnd_1812352 := by
    simpa [prefixWord, tailWord_1812352, baseEnd_1812352] using wordTrace_append hprefix tailTrace_1812352
  have hstable : (prefixWord ++ tailWord_1812352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812352).length < 2 ^ (prefixWord ++ tailWord_1812352).sum := by decide
  have hdescent : baseEnd_1812352 < baseStart_1812352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812355 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4]
def baseStart_1812355 : Nat := 118140960795 + 1812355 * 2 ^ 59
def prefixEnd_1812355 : Nat := 4983230072969 + 3 ^ 40 * 1812355 * 2
def baseEnd_1812355 : Nat := 930609231579361886427637

theorem tailTrace_1812355 : CollatzResearch.WordTrace tailWord_1812355 prefixEnd_1812355 930609231579361886427637 := by
  unfold tailWord_1812355
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102017349154835436518519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44068011566103223624345679 66102017349154835436518519)
  ·
    refine ⟨99153026023732253154777779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66102017349154835436518519 99153026023732253154777779)
    ·
      refine ⟨148729539035598379732166669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99153026023732253154777779 148729539035598379732166669)
      ·
        refine ⟨55773577138349392399562501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148729539035598379732166669 55773577138349392399562501)
        ·
          refine ⟨10457545713440511074917969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55773577138349392399562501 10457545713440511074917969)
          ·
            refine ⟨7843159285080383306188477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457545713440511074917969 7843159285080383306188477)
            ·
              refine ⟨2941184731905143739820679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7843159285080383306188477 2941184731905143739820679)
              ·
                refine ⟨4411777097857715609731019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941184731905143739820679 4411777097857715609731019)
                ·
                  refine ⟨6617665646786573414596529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411777097857715609731019 6617665646786573414596529)
                  ·
                    refine ⟨4963249235089930060947397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617665646786573414596529 4963249235089930060947397)
                    ·
                      refine ⟨930609231579361886427637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4963249235089930060947397 930609231579361886427637)
                      ·
                        rfl

theorem cell23_1812355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_1812355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812355 prefixEnd_1812355 := by exact prefixLift 1812355
  have htrace : WordTrace (prefixWord ++ tailWord_1812355) baseStart_1812355 baseEnd_1812355 := by
    simpa [prefixWord, tailWord_1812355, baseEnd_1812355] using wordTrace_append hprefix tailTrace_1812355
  have hstable : (prefixWord ++ tailWord_1812355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812355).length < 2 ^ (prefixWord ++ tailWord_1812355).sum := by decide
  have hdescent : baseEnd_1812355 < baseStart_1812355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812408 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1812408 : Nat := 118140960795 + 1812408 * 2 ^ 59
def prefixEnd_1812408 : Nat := 4983230072969 + 3 ^ 40 * 1812408 * 2
def baseEnd_1812408 : Nat := 310212148684683393021631

theorem tailTrace_1812408 : CollatzResearch.WordTrace tailWord_1812408 prefixEnd_1812408 310212148684683393021631 := by
  unfold tailWord_1812408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33051975208981412744098939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44069300278641883658798585 33051975208981412744098939)
  ·
    refine ⟨49577962813472119116148409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33051975208981412744098939 49577962813472119116148409)
    ·
      refine ⟨37183472110104089337111307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49577962813472119116148409 37183472110104089337111307)
      ·
        refine ⟨55775208165156134005666961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37183472110104089337111307 55775208165156134005666961)
        ·
          refine ⟨41831406123867100504250221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55775208165156134005666961 41831406123867100504250221)
          ·
            refine ⟨15686777296450162689093833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41831406123867100504250221 15686777296450162689093833)
            ·
              refine ⟨11765082972337622016820375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15686777296450162689093833 11765082972337622016820375)
              ·
                refine ⟨17647624458506433025230563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11765082972337622016820375 17647624458506433025230563)
                ·
                  refine ⟨26471436687759649537845845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17647624458506433025230563 26471436687759649537845845)
                  ·
                    refine ⟨310212148684683393021631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26471436687759649537845845 310212148684683393021631)
                    ·
                      rfl

theorem cell23_1812408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1812408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812408 prefixEnd_1812408 := by exact prefixLift 1812408
  have htrace : WordTrace (prefixWord ++ tailWord_1812408) baseStart_1812408 baseEnd_1812408 := by
    simpa [prefixWord, tailWord_1812408, baseEnd_1812408] using wordTrace_append hprefix tailTrace_1812408
  have hstable : (prefixWord ++ tailWord_1812408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812408).length < 2 ^ (prefixWord ++ tailWord_1812408).sum := by decide
  have hdescent : baseEnd_1812408 < baseStart_1812408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812432 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2]
def baseStart_1812432 : Nat := 118140960795 + 1812432 * 2 ^ 59
def prefixEnd_1812432 : Nat := 4983230072969 + 3 ^ 40 * 1812432 * 2
def baseEnd_1812432 : Nat := 930648769589758085164783

theorem tailTrace_1812432 : CollatzResearch.WordTrace tailWord_1812432 prefixEnd_1812432 930648769589758085164783 := by
  unfold tailWord_1812432
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052412884937938793535775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44069883846583918391381033 33052412884937938793535775)
  ·
    refine ⟨49578619327406908190303663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33052412884937938793535775 49578619327406908190303663)
    ·
      refine ⟨74367928991110362285455495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49578619327406908190303663 74367928991110362285455495)
      ·
        refine ⟨111551893486665543428183243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74367928991110362285455495 111551893486665543428183243)
        ·
          refine ⟨167327840229998315142274865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111551893486665543428183243 167327840229998315142274865)
          ·
            refine ⟨125495880172498736356706149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167327840229998315142274865 125495880172498736356706149)
            ·
              refine ⟨23530477532343513066882403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125495880172498736356706149 23530477532343513066882403)
              ·
                refine ⟨35295716298515269600323605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23530477532343513066882403 35295716298515269600323605)
                ·
                  refine ⟨1654486701492903262515169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35295716298515269600323605 1654486701492903262515169)
                  ·
                    refine ⟨1240865026119677446886377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654486701492903262515169 1240865026119677446886377)
                    ·
                      refine ⟨930648769589758085164783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240865026119677446886377 930648769589758085164783)
                      ·
                        rfl

theorem cell23_1812432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2].length) (baseStart_1812432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812432 prefixEnd_1812432 := by exact prefixLift 1812432
  have htrace : WordTrace (prefixWord ++ tailWord_1812432) baseStart_1812432 baseEnd_1812432 := by
    simpa [prefixWord, tailWord_1812432, baseEnd_1812432] using wordTrace_append hprefix tailTrace_1812432
  have hstable : (prefixWord ++ tailWord_1812432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812432).length < 2 ^ (prefixWord ++ tailWord_1812432).sum := by decide
  have hdescent : baseEnd_1812432 < baseStart_1812432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812436 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1812436 : Nat := 118140960795 + 1812436 * 2 ^ 59
def prefixEnd_1812436 : Nat := 4983230072969 + 3 ^ 40 * 1812436 * 2
def baseEnd_1812436 : Nat := 930650823512376069514765

theorem tailTrace_1812436 : CollatzResearch.WordTrace tailWord_1812436 prefixEnd_1812436 930650823512376069514765 := by
  unfold tailWord_1812436
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052485830930693135108581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44069981107907590846811441 33052485830930693135108581)
  ·
    refine ⟨6197341093299504962832859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33052485830930693135108581 6197341093299504962832859)
    ·
      refine ⟨9296011639949257444249289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197341093299504962832859 9296011639949257444249289)
      ·
        refine ⟨6972008729961943083186967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9296011639949257444249289 6972008729961943083186967)
        ·
          refine ⟨10458013094942914624780451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972008729961943083186967 10458013094942914624780451)
          ·
            refine ⟨15687019642414371937170677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458013094942914624780451 15687019642414371937170677)
            ·
              refine ⟨1470658091476347369109751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15687019642414371937170677 1470658091476347369109751)
              ·
                refine ⟨2205987137214521053664627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470658091476347369109751 2205987137214521053664627)
                ·
                  refine ⟨3308980705821781580496941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205987137214521053664627 3308980705821781580496941)
                  ·
                    refine ⟨1240867764683168092686353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3308980705821781580496941 1240867764683168092686353)
                    ·
                      refine ⟨930650823512376069514765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240867764683168092686353 930650823512376069514765)
                      ·
                        rfl

theorem cell23_1812436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1812436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812436 prefixEnd_1812436 := by exact prefixLift 1812436
  have htrace : WordTrace (prefixWord ++ tailWord_1812436) baseStart_1812436 baseEnd_1812436 := by
    simpa [prefixWord, tailWord_1812436, baseEnd_1812436] using wordTrace_append hprefix tailTrace_1812436
  have hstable : (prefixWord ++ tailWord_1812436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812436).length < 2 ^ (prefixWord ++ tailWord_1812436).sum := by decide
  have hdescent : baseEnd_1812436 < baseStart_1812436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812444 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1812444 : Nat := 118140960795 + 1812444 * 2 ^ 59
def prefixEnd_1812444 : Nat := 4983230072969 + 3 ^ 40 * 1812444 * 2
def baseEnd_1812444 : Nat := 930654931357612038214729

theorem tailTrace_1812444 : CollatzResearch.WordTrace tailWord_1812444 prefixEnd_1812444 930654931357612038214729 := by
  unfold tailWord_1812444
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052631722916201818254193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44070175630554935757672257 33052631722916201818254193)
  ·
    refine ⟨24789473792187151363690645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33052631722916201818254193 24789473792187151363690645)
    ·
      refine ⟨1162006584008772720172999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24789473792187151363690645 1162006584008772720172999)
      ·
        refine ⟨1743009876013159080259499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162006584008772720172999 1743009876013159080259499)
        ·
          refine ⟨2614514814019738620389249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743009876013159080259499 2614514814019738620389249)
          ·
            refine ⟨1960886110514803965291937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614514814019738620389249 1960886110514803965291937)
            ·
              refine ⟨1470664582886102973968953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960886110514803965291937 1470664582886102973968953)
              ·
                refine ⟨1102998437164577230476715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470664582886102973968953 1102998437164577230476715)
                ·
                  refine ⟨1654497655746865845715073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102998437164577230476715 1654497655746865845715073)
                  ·
                    refine ⟨1240873241810149384286305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654497655746865845715073 1240873241810149384286305)
                    ·
                      refine ⟨930654931357612038214729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240873241810149384286305 930654931357612038214729)
                      ·
                        rfl

theorem cell23_1812444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1812444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812444 prefixEnd_1812444 := by exact prefixLift 1812444
  have htrace : WordTrace (prefixWord ++ tailWord_1812444) baseStart_1812444 baseEnd_1812444 := by
    simpa [prefixWord, tailWord_1812444, baseEnd_1812444] using wordTrace_append hprefix tailTrace_1812444
  have hstable : (prefixWord ++ tailWord_1812444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812444).length < 2 ^ (prefixWord ++ tailWord_1812444).sum := by decide
  have hdescent : baseEnd_1812444 < baseStart_1812444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812448 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1812448 : Nat := 118140960795 + 1812448 * 2 ^ 59
def prefixEnd_1812448 : Nat := 4983230072969 + 3 ^ 40 * 1812448 * 2
def baseEnd_1812448 : Nat := 930656985280230022564709

theorem tailTrace_1812448 : CollatzResearch.WordTrace tailWord_1812448 prefixEnd_1812448 930656985280230022564709 := by
  unfold tailWord_1812448
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052704668908956159826999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44070272891878608213102665 33052704668908956159826999)
  ·
    refine ⟨49579057003363434239740499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33052704668908956159826999 49579057003363434239740499)
    ·
      refine ⟨74368585505045151359610749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49579057003363434239740499 74368585505045151359610749)
      ·
        refine ⟨27888219564391931759854031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74368585505045151359610749 27888219564391931759854031)
        ·
          refine ⟨41832329346587897639781047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27888219564391931759854031 41832329346587897639781047)
          ·
            refine ⟨62748494019881846459671571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41832329346587897639781047 62748494019881846459671571)
            ·
              refine ⟨94122741029822769689507357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62748494019881846459671571 94122741029822769689507357)
              ·
                refine ⟨35296027886183538633565259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94122741029822769689507357 35296027886183538633565259)
                ·
                  refine ⟨52944041829275307950347889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35296027886183538633565259 52944041829275307950347889)
                  ·
                    refine ⟨39708031371956480962760917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52944041829275307950347889 39708031371956480962760917)
                    ·
                      refine ⟨930656985280230022564709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39708031371956480962760917 930656985280230022564709)
                      ·
                        rfl

theorem cell23_1812448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1812448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812448 prefixEnd_1812448 := by exact prefixLift 1812448
  have htrace : WordTrace (prefixWord ++ tailWord_1812448) baseStart_1812448 baseEnd_1812448 := by
    simpa [prefixWord, tailWord_1812448, baseEnd_1812448] using wordTrace_append hprefix tailTrace_1812448
  have hstable : (prefixWord ++ tailWord_1812448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812448).length < 2 ^ (prefixWord ++ tailWord_1812448).sum := by decide
  have hdescent : baseEnd_1812448 < baseStart_1812448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812449 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_1812449 : Nat := 118140960795 + 1812449 * 2 ^ 59
def prefixEnd_1812449 : Nat := 4983230072969 + 3 ^ 40 * 1812449 * 2
def baseEnd_1812449 : Nat := 930657498760884518652205

theorem tailTrace_1812449 : CollatzResearch.WordTrace tailWord_1812449 prefixEnd_1812449 930657498760884518652205 := by
  unfold tailWord_1812449
  simp only [CollatzResearch.WordTrace]
  refine ⟨66105445810814289490440401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44070297207209526326960267 66105445810814289490440401)
  ·
    refine ⟨49579084358110717117830301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66105445810814289490440401 49579084358110717117830301)
    ·
      refine ⟨18592156634291518919186363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49579084358110717117830301 18592156634291518919186363)
      ·
        refine ⟨27888234951437278378779545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18592156634291518919186363 27888234951437278378779545)
        ·
          refine ⟨20916176213577958784084659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27888234951437278378779545 20916176213577958784084659)
          ·
            refine ⟨31374264320366938176126989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20916176213577958784084659 31374264320366938176126989)
            ·
              refine ⟨11765349120137601816047621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31374264320366938176126989 11765349120137601816047621)
              ·
                refine ⟨2206002960025800340508929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11765349120137601816047621 2206002960025800340508929)
                ·
                  refine ⟨1654502220019350255381697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206002960025800340508929 1654502220019350255381697)
                  ·
                    refine ⟨1240876665014512691536273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654502220019350255381697 1240876665014512691536273)
                    ·
                      refine ⟨930657498760884518652205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240876665014512691536273 930657498760884518652205)
                      ·
                        rfl

theorem cell23_1812449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_1812449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812449 prefixEnd_1812449 := by exact prefixLift 1812449
  have htrace : WordTrace (prefixWord ++ tailWord_1812449) baseStart_1812449 baseEnd_1812449 := by
    simpa [prefixWord, tailWord_1812449, baseEnd_1812449] using wordTrace_append hprefix tailTrace_1812449
  have hstable : (prefixWord ++ tailWord_1812449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812449).length < 2 ^ (prefixWord ++ tailWord_1812449).sum := by decide
  have hdescent : baseEnd_1812449 < baseStart_1812449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812462 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1812462 : Nat := 118140960795 + 1812462 * 2 ^ 59
def prefixEnd_1812462 : Nat := 4983230072969 + 3 ^ 40 * 1812462 * 2
def baseEnd_1812462 : Nat := 930664174009392967789645

theorem tailTrace_1812462 : CollatzResearch.WordTrace tailWord_1812462 prefixEnd_1812462 930664174009392967789645 := by
  unfold tailWord_1812462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263239994970899088832955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44070613306511461807109093 8263239994970899088832955)
  ·
    refine ⟨12394859992456348633249433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8263239994970899088832955 12394859992456348633249433)
    ·
      refine ⟨9296144994342261474937075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12394859992456348633249433 9296144994342261474937075)
      ·
        refine ⟨13944217491513392212405613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296144994342261474937075 13944217491513392212405613)
        ·
          refine ⟨5229081559317522079652105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13944217491513392212405613 5229081559317522079652105)
          ·
            refine ⟨3921811169488141559739079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229081559317522079652105 3921811169488141559739079)
            ·
              refine ⟨5882716754232212339608619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921811169488141559739079 5882716754232212339608619)
              ·
                refine ⟨8824075131348318509412929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882716754232212339608619 8824075131348318509412929)
                ·
                  refine ⟨6618056348511238882059697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824075131348318509412929 6618056348511238882059697)
                  ·
                    refine ⟨4963542261383429161544773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618056348511238882059697 4963542261383429161544773)
                    ·
                      refine ⟨930664174009392967789645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4963542261383429161544773 930664174009392967789645)
                      ·
                        rfl

theorem cell23_1812462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1812462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812462 prefixEnd_1812462 := by exact prefixLift 1812462
  have htrace : WordTrace (prefixWord ++ tailWord_1812462) baseStart_1812462 baseEnd_1812462 := by
    simpa [prefixWord, tailWord_1812462, baseEnd_1812462] using wordTrace_append hprefix tailTrace_1812462
  have hstable : (prefixWord ++ tailWord_1812462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812462).length < 2 ^ (prefixWord ++ tailWord_1812462).sum := by decide
  have hdescent : baseEnd_1812462 < baseStart_1812462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812485 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1812485 : Nat := 118140960795 + 1812485 * 2 ^ 59
def prefixEnd_1812485 : Nat := 4983230072969 + 3 ^ 40 * 1812485 * 2
def baseEnd_1812485 : Nat := 310225328021482125934013

theorem tailTrace_1812485 : CollatzResearch.WordTrace tailWord_1812485 prefixEnd_1812485 310225328021482125934013 := by
  unfold tailWord_1812485
  simp only [CollatzResearch.WordTrace]
  refine ⟨66106758838683867638750909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44071172559122578425833939 66106758838683867638750909)
  ·
    refine ⟨24790034564506450364531591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66106758838683867638750909 24790034564506450364531591)
    ·
      refine ⟨37185051846759675546797387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24790034564506450364531591 37185051846759675546797387)
      ·
        refine ⟨55777577770139513320196081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37185051846759675546797387 55777577770139513320196081)
        ·
          refine ⟨41833183327604634990147061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55777577770139513320196081 41833183327604634990147061)
          ·
            refine ⟨3921860936962934530326287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41833183327604634990147061 3921860936962934530326287)
            ·
              refine ⟨5882791405444401795489431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921860936962934530326287 5882791405444401795489431)
              ·
                refine ⟨8824187108166602693234147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882791405444401795489431 8824187108166602693234147)
                ·
                  refine ⟨13236280662249904039851221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824187108166602693234147 13236280662249904039851221)
                  ·
                    refine ⟨310225328021482125934013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13236280662249904039851221 310225328021482125934013)
                    ·
                      rfl

theorem cell23_1812485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1812485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812485 prefixEnd_1812485 := by exact prefixLift 1812485
  have htrace : WordTrace (prefixWord ++ tailWord_1812485) baseStart_1812485 baseEnd_1812485 := by
    simpa [prefixWord, tailWord_1812485, baseEnd_1812485] using wordTrace_append hprefix tailTrace_1812485
  have hstable : (prefixWord ++ tailWord_1812485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812485).length < 2 ^ (prefixWord ++ tailWord_1812485).sum := by decide
  have hdescent : baseEnd_1812485 < baseStart_1812485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812505 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1812505 : Nat := 118140960795 + 1812505 * 2 ^ 59
def prefixEnd_1812505 : Nat := 4983230072969 + 3 ^ 40 * 1812505 * 2
def baseEnd_1812505 : Nat := 930686253677536299551947

theorem tailTrace_1812505 : CollatzResearch.WordTrace tailWord_1812505 prefixEnd_1812505 930686253677536299551947 := by
  unfold tailWord_1812505
  simp only [CollatzResearch.WordTrace]
  refine ⟨66107488298611411054478969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44071658865740940702985979 66107488298611411054478969)
  ·
    refine ⟨49580616223958558290859227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66107488298611411054478969 49580616223958558290859227)
    ·
      refine ⟨74370924335937837436288841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49580616223958558290859227 74370924335937837436288841)
      ·
        refine ⟨55778193251953378077216631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74370924335937837436288841 55778193251953378077216631)
        ·
          refine ⟨83667289877930067115824947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55778193251953378077216631 83667289877930067115824947)
          ·
            refine ⟨125500934816895100673737421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83667289877930067115824947 125500934816895100673737421)
            ·
              refine ⟨47062850556335662752651533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125500934816895100673737421 47062850556335662752651533)
              ·
                refine ⟨17648568958625873532244325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47062850556335662752651533 17648568958625873532244325)
                ·
                  refine ⟨3309106679742351287295811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17648568958625873532244325 3309106679742351287295811)
                  ·
                    refine ⟨4963660019613526930943717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309106679742351287295811 4963660019613526930943717)
                    ·
                      refine ⟨930686253677536299551947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4963660019613526930943717 930686253677536299551947)
                      ·
                        rfl

theorem cell23_1812505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1812505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812505 prefixEnd_1812505 := by exact prefixLift 1812505
  have htrace : WordTrace (prefixWord ++ tailWord_1812505) baseStart_1812505 baseEnd_1812505 := by
    simpa [prefixWord, tailWord_1812505, baseEnd_1812505] using wordTrace_append hprefix tailTrace_1812505
  have hstable : (prefixWord ++ tailWord_1812505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812505).length < 2 ^ (prefixWord ++ tailWord_1812505).sum := by decide
  have hdescent : baseEnd_1812505 < baseStart_1812505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812522 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1812522 : Nat := 118140960795 + 1812522 * 2 ^ 59
def prefixEnd_1812522 : Nat := 4983230072969 + 3 ^ 40 * 1812522 * 2
def baseEnd_1812522 : Nat := 930694982848662733039369

theorem tailTrace_1812522 : CollatzResearch.WordTrace tailWord_1812522 prefixEnd_1812522 930694982848662733039369 := by
  unfold tailWord_1812522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527027084887455739461955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44072072226366548638565213 16527027084887455739461955)
  ·
    refine ⟨24790540627331183609192933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16527027084887455739461955 24790540627331183609192933)
    ·
      refine ⟨4648226367624596926723675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24790540627331183609192933 4648226367624596926723675)
      ·
        refine ⟨6972339551436895390085513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648226367624596926723675 6972339551436895390085513)
        ·
          refine ⟨5229254663577671542564135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972339551436895390085513 5229254663577671542564135)
          ·
            refine ⟨7843881995366507313846203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229254663577671542564135 7843881995366507313846203)
            ·
              refine ⟨11765822993049760970769305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843881995366507313846203 11765822993049760970769305)
              ·
                refine ⟨8824367244787320728076979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11765822993049760970769305 8824367244787320728076979)
                ·
                  refine ⟨13236550867180981092115469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824367244787320728076979 13236550867180981092115469)
                  ·
                    refine ⟨4963706575192867909543301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13236550867180981092115469 4963706575192867909543301)
                    ·
                      refine ⟨930694982848662733039369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4963706575192867909543301 930694982848662733039369)
                      ·
                        rfl

theorem cell23_1812522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1812522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812522 prefixEnd_1812522 := by exact prefixLift 1812522
  have htrace : WordTrace (prefixWord ++ tailWord_1812522) baseStart_1812522 baseEnd_1812522 := by
    simpa [prefixWord, tailWord_1812522, baseEnd_1812522] using wordTrace_append hprefix tailTrace_1812522
  have hstable : (prefixWord ++ tailWord_1812522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812522).length < 2 ^ (prefixWord ++ tailWord_1812522).sum := by decide
  have hdescent : baseEnd_1812522 < baseStart_1812522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812555 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3]
def baseStart_1812555 : Nat := 118140960795 + 1812555 * 2 ^ 59
def prefixEnd_1812555 : Nat := 4983230072969 + 3 ^ 40 * 1812555 * 2
def baseEnd_1812555 : Nat := 930711927710261103926717

theorem tailTrace_1812555 : CollatzResearch.WordTrace tailWord_1812555 prefixEnd_1812555 930711927710261103926717 := by
  unfold tailWord_1812555
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109311948430269593799119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44072874632286846395866079 66109311948430269593799119)
  ·
    refine ⟨99163967922645404390698679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66109311948430269593799119 99163967922645404390698679)
    ·
      refine ⟨148745951883968106586048019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99163967922645404390698679 148745951883968106586048019)
      ·
        refine ⟨223118927825952159879072029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148745951883968106586048019 223118927825952159879072029)
        ·
          refine ⟨83669597934732059954652011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223118927825952159879072029 83669597934732059954652011)
          ·
            refine ⟨125504396902098089931978017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83669597934732059954652011 125504396902098089931978017)
            ·
              refine ⟨94128297676573567448983513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125504396902098089931978017 94128297676573567448983513)
              ·
                refine ⟨70596223257430175586737635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94128297676573567448983513 70596223257430175586737635)
                ·
                  refine ⟨105894334886145263380106453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70596223257430175586737635 105894334886145263380106453)
                  ·
                    refine ⟨2481898473894029610471245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 105894334886145263380106453 2481898473894029610471245)
                    ·
                      refine ⟨930711927710261103926717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2481898473894029610471245 930711927710261103926717)
                      ·
                        rfl

theorem cell23_1812555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 3].length) (baseStart_1812555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812555 prefixEnd_1812555 := by exact prefixLift 1812555
  have htrace : WordTrace (prefixWord ++ tailWord_1812555) baseStart_1812555 baseEnd_1812555 := by
    simpa [prefixWord, tailWord_1812555, baseEnd_1812555] using wordTrace_append hprefix tailTrace_1812555
  have hstable : (prefixWord ++ tailWord_1812555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812555).length < 2 ^ (prefixWord ++ tailWord_1812555).sum := by decide
  have hdescent : baseEnd_1812555 < baseStart_1812555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812589 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1812589 : Nat := 118140960795 + 1812589 * 2 ^ 59
def prefixEnd_1812589 : Nat := 4983230072969 + 3 ^ 40 * 1812589 * 2
def baseEnd_1812589 : Nat := 930729386052513970901561

theorem tailTrace_1812589 : CollatzResearch.WordTrace tailWord_1812589 prefixEnd_1812589 930729386052513970901561 := by
  unfold tailWord_1812589
  simp only [CollatzResearch.WordTrace]
  refine ⟨66110552030307093400536821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44073701353538062267024547 66110552030307093400536821)
  ·
    refine ⟨6197864252841290006300327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66110552030307093400536821 6197864252841290006300327)
    ·
      refine ⟨9296796379261935009450491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197864252841290006300327 9296796379261935009450491)
      ·
        refine ⟨13945194568892902514175737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296796379261935009450491 13945194568892902514175737)
        ·
          refine ⟨10458895926669676885631803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13945194568892902514175737 10458895926669676885631803)
          ·
            refine ⟨15688343890004515328447705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458895926669676885631803 15688343890004515328447705)
            ·
              refine ⟨11766257917503386496335779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15688343890004515328447705 11766257917503386496335779)
              ·
                refine ⟨17649386876255079744503669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11766257917503386496335779 17649386876255079744503669)
                ·
                  refine ⟨1654630019648913726047219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17649386876255079744503669 1654630019648913726047219)
                  ·
                    refine ⟨2481945029473370589070829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1654630019648913726047219 2481945029473370589070829)
                    ·
                      refine ⟨930729386052513970901561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2481945029473370589070829 930729386052513970901561)
                      ·
                        rfl

theorem cell23_1812589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1812589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812589 prefixEnd_1812589 := by exact prefixLift 1812589
  have htrace : WordTrace (prefixWord ++ tailWord_1812589) baseStart_1812589 baseEnd_1812589 := by
    simpa [prefixWord, tailWord_1812589, baseEnd_1812589] using wordTrace_append hprefix tailTrace_1812589
  have hstable : (prefixWord ++ tailWord_1812589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812589).length < 2 ^ (prefixWord ++ tailWord_1812589).sum := by decide
  have hdescent : baseEnd_1812589 < baseStart_1812589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812592 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_1812592 : Nat := 118140960795 + 1812592 * 2 ^ 59
def prefixEnd_1812592 : Nat := 4983230072969 + 3 ^ 40 * 1812592 * 2
def baseEnd_1812592 : Nat := 310243642164825819721349

theorem tailTrace_1812592 : CollatzResearch.WordTrace tailWord_1812592 prefixEnd_1812592 310243642164825819721349 := by
  unfold tailWord_1812592
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055330724648112456448015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44073774299530816608597353 33055330724648112456448015)
  ·
    refine ⟨49582996086972168684672023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33055330724648112456448015 49582996086972168684672023)
    ·
      refine ⟨74374494130458253027008035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49582996086972168684672023 74374494130458253027008035)
      ·
        refine ⟨111561741195687379540512053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74374494130458253027008035 111561741195687379540512053)
        ·
          refine ⟨10458913237095691831923005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111561741195687379540512053 10458913237095691831923005)
          ·
            refine ⟨3922092463910884436971127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10458913237095691831923005 3922092463910884436971127)
            ·
              refine ⟨5883138695866326655456691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922092463910884436971127 5883138695866326655456691)
              ·
                refine ⟨8824708043799489983185037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883138695866326655456691 8824708043799489983185037)
                ·
                  refine ⟨3309265516424808743694389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8824708043799489983185037 3309265516424808743694389)
                  ·
                    refine ⟨310243642164825819721349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3309265516424808743694389 310243642164825819721349)
                    ·
                      rfl

theorem cell23_1812592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_1812592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812592 prefixEnd_1812592 := by exact prefixLift 1812592
  have htrace : WordTrace (prefixWord ++ tailWord_1812592) baseStart_1812592 baseEnd_1812592 := by
    simpa [prefixWord, tailWord_1812592, baseEnd_1812592] using wordTrace_append hprefix tailTrace_1812592
  have hstable : (prefixWord ++ tailWord_1812592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812592).length < 2 ^ (prefixWord ++ tailWord_1812592).sum := by decide
  have hdescent : baseEnd_1812592 < baseStart_1812592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812599 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_1812599 : Nat := 118140960795 + 1812599 * 2 ^ 59
def prefixEnd_1812599 : Nat := 4983230072969 + 3 ^ 40 * 1812599 * 2
def baseEnd_1812599 : Nat := 930734520859058931776515

theorem tailTrace_1812599 : CollatzResearch.WordTrace tailWord_1812599 prefixEnd_1812599 930734520859058931776515 := by
  unfold tailWord_1812599
  simp only [CollatzResearch.WordTrace]
  refine ⟨66110916760270865108400851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44073944506847243405600567 66110916760270865108400851)
  ·
    refine ⟨99166375140406297662601277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66110916760270865108400851 99166375140406297662601277)
    ·
      refine ⟨37187390677652361623475479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99166375140406297662601277 37187390677652361623475479)
      ·
        refine ⟨55781086016478542435213219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37187390677652361623475479 55781086016478542435213219)
        ·
          refine ⟨83671629024717813652819829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55781086016478542435213219 83671629024717813652819829)
          ·
            refine ⟨7844215221067295029951859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83671629024717813652819829 7844215221067295029951859)
            ·
              refine ⟨11766322831600942544927789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844215221067295029951859 11766322831600942544927789)
              ·
                refine ⟨4412371061850353454347921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11766322831600942544927789 4412371061850353454347921)
                ·
                  refine ⟨3309278296387765090760941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412371061850353454347921 3309278296387765090760941)
                  ·
                    refine ⟨1240979361145411909035353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309278296387765090760941 1240979361145411909035353)
                    ·
                      refine ⟨930734520859058931776515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240979361145411909035353 930734520859058931776515)
                      ·
                        rfl

theorem cell23_1812599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_1812599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812599 prefixEnd_1812599 := by exact prefixLift 1812599
  have htrace : WordTrace (prefixWord ++ tailWord_1812599) baseStart_1812599 baseEnd_1812599 := by
    simpa [prefixWord, tailWord_1812599, baseEnd_1812599] using wordTrace_append hprefix tailTrace_1812599
  have hstable : (prefixWord ++ tailWord_1812599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812599).length < 2 ^ (prefixWord ++ tailWord_1812599).sum := by decide
  have hdescent : baseEnd_1812599 < baseStart_1812599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812616 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1812616 : Nat := 118140960795 + 1812616 * 2 ^ 59
def prefixEnd_1812616 : Nat := 4983230072969 + 3 ^ 40 * 1812616 * 2
def baseEnd_1812616 : Nat := 930743250030185365263937

theorem tailTrace_1812616 : CollatzResearch.WordTrace tailWord_1812616 prefixEnd_1812616 930743250030185365263937 := by
  unfold tailWord_1812616
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055768400604638505884851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44074357867472851341179801 33055768400604638505884851)
  ·
    refine ⟨49583652600906957758827277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33055768400604638505884851 49583652600906957758827277)
    ·
      refine ⟨18593869725340109159560229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49583652600906957758827277 18593869725340109159560229)
      ·
        refine ⟨3486350573501270467417543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18593869725340109159560229 3486350573501270467417543)
        ·
          refine ⟨5229525860251905701126315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486350573501270467417543 5229525860251905701126315)
          ·
            refine ⟨7844288790377858551689473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229525860251905701126315 7844288790377858551689473)
            ·
              refine ⟨5883216592783393913767105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844288790377858551689473 5883216592783393913767105)
              ·
                refine ⟨4412412444587545435325329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5883216592783393913767105 4412412444587545435325329)
                ·
                  refine ⟨3309309333440659076493997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412412444587545435325329 3309309333440659076493997)
                  ·
                    refine ⟨1240991000040247153685249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309309333440659076493997 1240991000040247153685249)
                    ·
                      refine ⟨930743250030185365263937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1240991000040247153685249 930743250030185365263937)
                      ·
                        rfl

theorem cell23_1812616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1812616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812616 prefixEnd_1812616 := by exact prefixLift 1812616
  have htrace : WordTrace (prefixWord ++ tailWord_1812616) baseStart_1812616 baseEnd_1812616 := by
    simpa [prefixWord, tailWord_1812616, baseEnd_1812616] using wordTrace_append hprefix tailTrace_1812616
  have hstable : (prefixWord ++ tailWord_1812616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812616).length < 2 ^ (prefixWord ++ tailWord_1812616).sum := by decide
  have hdescent : baseEnd_1812616 < baseStart_1812616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812639 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 1, 6]
def baseStart_1812639 : Nat := 118140960795 + 1812639 * 2 ^ 59
def prefixEnd_1812639 : Nat := 4983230072969 + 3 ^ 40 * 1812639 * 2
def baseEnd_1812639 : Nat := 310251686695079591758777

theorem tailTrace_1812639 : CollatzResearch.WordTrace tailWord_1812639 prefixEnd_1812639 310251686695079591758777 := by
  unfold tailWord_1812639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66112375680125951939856971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44074917120083967959904647 66112375680125951939856971)
  ·
    refine ⟨99168563520188927909785457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66112375680125951939856971 99168563520188927909785457)
    ·
      refine ⟨74376422640141695932339093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99168563520188927909785457 74376422640141695932339093)
      ·
        refine ⟨3486394811256641996828395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74376422640141695932339093 3486394811256641996828395)
        ·
          refine ⟨5229592216884962995242593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486394811256641996828395 5229592216884962995242593)
          ·
            refine ⟨3922194162663722246431945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5229592216884962995242593 3922194162663722246431945)
            ·
              refine ⟨2941645621997791684823959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922194162663722246431945 2941645621997791684823959)
              ·
                refine ⟨4412468432996687527235939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941645621997791684823959 4412468432996687527235939)
                ·
                  refine ⟨6618702649495031290853909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412468432996687527235939 6618702649495031290853909)
                  ·
                    refine ⟨310251686695079591758777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6618702649495031290853909 310251686695079591758777)
                    ·
                      rfl

theorem cell23_1812639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_1812639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812639 prefixEnd_1812639 := by exact prefixLift 1812639
  have htrace : WordTrace (prefixWord ++ tailWord_1812639) baseStart_1812639 baseEnd_1812639 := by
    simpa [prefixWord, tailWord_1812639, baseEnd_1812639] using wordTrace_append hprefix tailTrace_1812639
  have hstable : (prefixWord ++ tailWord_1812639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812639).length < 2 ^ (prefixWord ++ tailWord_1812639).sum := by decide
  have hdescent : baseEnd_1812639 < baseStart_1812639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812650 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1812650 : Nat := 118140960795 + 1812650 * 2 ^ 59
def prefixEnd_1812650 : Nat := 4983230072969 + 3 ^ 40 * 1812650 * 2
def baseEnd_1812650 : Nat := 930760708372438232238781

theorem tailTrace_1812650 : CollatzResearch.WordTrace tailWord_1812650 prefixEnd_1812650 930760708372438232238781 := by
  unfold tailWord_1812650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528194220771525204626851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44075184588724067212338269 16528194220771525204626851)
  ·
    refine ⟨24792291331157287806940277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16528194220771525204626851 24792291331157287806940277)
    ·
      refine ⟨2324277312295995731900651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24792291331157287806940277 2324277312295995731900651)
      ·
        refine ⟨3486415968443993597850977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324277312295995731900651 3486415968443993597850977)
        ·
          refine ⟨2614811976332995198388233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3486415968443993597850977 2614811976332995198388233)
          ·
            refine ⟨1961108982249746398791175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614811976332995198388233 1961108982249746398791175)
            ·
              refine ⟨2941663473374619598186763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961108982249746398791175 2941663473374619598186763)
              ·
                refine ⟨4412495210061929397280145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941663473374619598186763 4412495210061929397280145)
                ·
                  refine ⟨3309371407546447047960109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412495210061929397280145 3309371407546447047960109)
                  ·
                    refine ⟨1241014277829917642985041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309371407546447047960109 1241014277829917642985041)
                    ·
                      refine ⟨930760708372438232238781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241014277829917642985041 930760708372438232238781)
                      ·
                        rfl

theorem cell23_1812650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1812650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812650 prefixEnd_1812650 := by exact prefixLift 1812650
  have htrace : WordTrace (prefixWord ++ tailWord_1812650) baseStart_1812650 baseEnd_1812650 := by
    simpa [prefixWord, tailWord_1812650, baseEnd_1812650] using wordTrace_append hprefix tailTrace_1812650
  have hstable : (prefixWord ++ tailWord_1812650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812650).length < 2 ^ (prefixWord ++ tailWord_1812650).sum := by decide
  have hdescent : baseEnd_1812650 < baseStart_1812650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812660 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1812660 : Nat := 118140960795 + 1812660 * 2 ^ 59
def prefixEnd_1812660 : Nat := 4983230072969 + 3 ^ 40 * 1812660 * 2
def baseEnd_1812660 : Nat := 310255281059661064371245

theorem tailTrace_1812660 : CollatzResearch.WordTrace tailWord_1812660 prefixEnd_1812660 310255281059661064371245 := by
  unfold tailWord_1812660
  simp only [CollatzResearch.WordTrace]
  refine ⟨33056570806524936263185717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44075427742033248350914289 33056570806524936263185717)
  ·
    refine ⟨3099053513111712774673661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33056570806524936263185717 3099053513111712774673661)
    ·
      refine ⟨1162145067416892290502623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3099053513111712774673661 1162145067416892290502623)
      ·
        refine ⟨1743217601125338435753935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162145067416892290502623 1743217601125338435753935)
        ·
          refine ⟨2614826401688007653630903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743217601125338435753935 2614826401688007653630903)
          ·
            refine ⟨3922239602532011480446355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614826401688007653630903 3922239602532011480446355)
            ·
              refine ⟨5883359403798017220669533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922239602532011480446355 5883359403798017220669533)
              ·
                refine ⟨2206259776424256457751075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5883359403798017220669533 2206259776424256457751075)
                ·
                  refine ⟨3309389664636384686626613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206259776424256457751075 3309389664636384686626613)
                  ·
                    refine ⟨310255281059661064371245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3309389664636384686626613 310255281059661064371245)
                    ·
                      rfl

theorem cell23_1812660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1812660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812660 prefixEnd_1812660 := by exact prefixLift 1812660
  have htrace : WordTrace (prefixWord ++ tailWord_1812660) baseStart_1812660 baseEnd_1812660 := by
    simpa [prefixWord, tailWord_1812660, baseEnd_1812660] using wordTrace_append hprefix tailTrace_1812660
  have hstable : (prefixWord ++ tailWord_1812660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812660).length < 2 ^ (prefixWord ++ tailWord_1812660).sum := by decide
  have hdescent : baseEnd_1812660 < baseStart_1812660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812663 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 1, 2, 2]
def baseStart_1812663 : Nat := 118140960795 + 1812663 * 2 ^ 59
def prefixEnd_1812663 : Nat := 4983230072969 + 3 ^ 40 * 1812663 * 2
def baseEnd_1812663 : Nat := 930767383620946681376221

theorem tailTrace_1812663 : CollatzResearch.WordTrace tailWord_1812663 prefixEnd_1812663 930767383620946681376221 := by
  unfold tailWord_1812663
  simp only [CollatzResearch.WordTrace]
  refine ⟨66113251032039004038730643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44075500688026002692487095 66113251032039004038730643)
  ·
    refine ⟨99169876548058506058095965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66113251032039004038730643 99169876548058506058095965)
    ·
      refine ⟨37188703705521939771785987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99169876548058506058095965 37188703705521939771785987)
      ·
        refine ⟨55783055558282909657678981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37188703705521939771785987 55783055558282909657678981)
        ·
          refine ⟨10459322917178045560814809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55783055558282909657678981 10459322917178045560814809)
          ·
            refine ⟨7844492187883534170611107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10459322917178045560814809 7844492187883534170611107)
            ·
              refine ⟨11766738281825301255916661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844492187883534170611107 11766738281825301255916661)
              ·
                refine ⟨1103131713921121992742187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11766738281825301255916661 1103131713921121992742187)
                ·
                  refine ⟨1654697570881682989113281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103131713921121992742187 1654697570881682989113281)
                  ·
                    refine ⟨1241023178161262241834961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654697570881682989113281 1241023178161262241834961)
                    ·
                      refine ⟨930767383620946681376221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241023178161262241834961 930767383620946681376221)
                      ·
                        rfl

theorem cell23_1812663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_1812663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812663 prefixEnd_1812663 := by exact prefixLift 1812663
  have htrace : WordTrace (prefixWord ++ tailWord_1812663) baseStart_1812663 baseEnd_1812663 := by
    simpa [prefixWord, tailWord_1812663, baseEnd_1812663] using wordTrace_append hprefix tailTrace_1812663
  have hstable : (prefixWord ++ tailWord_1812663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812663).length < 2 ^ (prefixWord ++ tailWord_1812663).sum := by decide
  have hdescent : baseEnd_1812663 < baseStart_1812663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812666 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_1812666 : Nat := 118140960795 + 1812666 * 2 ^ 59
def prefixEnd_1812666 : Nat := 4983230072969 + 3 ^ 40 * 1812666 * 2
def baseEnd_1812666 : Nat := 930768924062910169638707

theorem tailTrace_1812666 : CollatzResearch.WordTrace tailWord_1812666 prefixEnd_1812666 930768924062910169638707 := by
  unfold tailWord_1812666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528340112757033887772463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44075573634018757034059901 16528340112757033887772463)
  ·
    refine ⟨24792510169135550831658695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16528340112757033887772463 24792510169135550831658695)
    ·
      refine ⟨37188765253703326247488043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24792510169135550831658695 37188765253703326247488043)
      ·
        refine ⟨55783147880554989371232065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37188765253703326247488043 55783147880554989371232065)
        ·
          refine ⟨41837360910416242028424049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55783147880554989371232065 41837360910416242028424049)
          ·
            refine ⟨31378020682812181521318037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41837360910416242028424049 31378020682812181521318037)
            ·
              refine ⟨1470844719506821008811783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31378020682812181521318037 1470844719506821008811783)
              ·
                refine ⟨2206267079260231513217675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470844719506821008811783 2206267079260231513217675)
                ·
                  refine ⟨3309400618890347269826513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206267079260231513217675 3309400618890347269826513)
                  ·
                    refine ⟨2482050464167760452369885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3309400618890347269826513 2482050464167760452369885)
                    ·
                      refine ⟨930768924062910169638707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482050464167760452369885 930768924062910169638707)
                      ·
                        rfl

theorem cell23_1812666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_1812666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812666 prefixEnd_1812666 := by exact prefixLift 1812666
  have htrace : WordTrace (prefixWord ++ tailWord_1812666) baseStart_1812666 baseEnd_1812666 := by
    simpa [prefixWord, tailWord_1812666, baseEnd_1812666] using wordTrace_append hprefix tailTrace_1812666
  have hstable : (prefixWord ++ tailWord_1812666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812666).length < 2 ^ (prefixWord ++ tailWord_1812666).sum := by decide
  have hdescent : baseEnd_1812666 < baseStart_1812666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812689 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_1812689 : Nat := 118140960795 + 1812689 * 2 ^ 59
def prefixEnd_1812689 : Nat := 4983230072969 + 3 ^ 40 * 1812689 * 2
def baseEnd_1812689 : Nat := 930780734117963579651101

theorem tailTrace_1812689 : CollatzResearch.WordTrace tailWord_1812689 prefixEnd_1812689 930780734117963579651101 := by
  unfold tailWord_1812689
  simp only [CollatzResearch.WordTrace]
  refine ⟨66114199329944810479177121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44076132886629873652784747 66114199329944810479177121)
  ·
    refine ⟨49585649497458607859382841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66114199329944810479177121 49585649497458607859382841)
    ·
      refine ⟨37189237123093955894537131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49585649497458607859382841 37189237123093955894537131)
      ·
        refine ⟨55783855684640933841805697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37189237123093955894537131 55783855684640933841805697)
        ·
          refine ⟨41837891763480700381354273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55783855684640933841805697 41837891763480700381354273)
          ·
            refine ⟨31378418822610525286015705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41837891763480700381354273 31378418822610525286015705)
            ·
              refine ⟨23533814116957893964511779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31378418822610525286015705 23533814116957893964511779)
              ·
                refine ⟨35300721175436840946767669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23533814116957893964511779 35300721175436840946767669)
                ·
                  refine ⟨3309442610197203838759469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35300721175436840946767669 3309442610197203838759469)
                  ·
                    refine ⟨1241040978823951439534801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309442610197203838759469 1241040978823951439534801)
                    ·
                      refine ⟨930780734117963579651101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241040978823951439534801 930780734117963579651101)
                      ·
                        rfl

theorem cell23_1812689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_1812689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812689 prefixEnd_1812689 := by exact prefixLift 1812689
  have htrace : WordTrace (prefixWord ++ tailWord_1812689) baseStart_1812689 baseEnd_1812689 := by
    simpa [prefixWord, tailWord_1812689, baseEnd_1812689] using wordTrace_append hprefix tailTrace_1812689
  have hstable : (prefixWord ++ tailWord_1812689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812689).length < 2 ^ (prefixWord ++ tailWord_1812689).sum := by decide
  have hdescent : baseEnd_1812689 < baseStart_1812689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812693 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1812693 : Nat := 118140960795 + 1812693 * 2 ^ 59
def prefixEnd_1812693 : Nat := 4983230072969 + 3 ^ 40 * 1812693 * 2
def baseEnd_1812693 : Nat := 930782788040581564001083

theorem tailTrace_1812693 : CollatzResearch.WordTrace tailWord_1812693 prefixEnd_1812693 930782788040581564001083 := by
  unfold tailWord_1812693
  simp only [CollatzResearch.WordTrace]
  refine ⟨66114345221930319162322733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44076230147953546108215155 66114345221930319162322733)
  ·
    refine ⟨24792879458223869685871025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66114345221930319162322733 24792879458223869685871025)
    ·
      refine ⟨18594659593667902264403269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24792879458223869685871025 18594659593667902264403269)
      ·
        refine ⟨3486498673812731674575613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18594659593667902264403269 3486498673812731674575613)
        ·
          refine ⟨1307437002679774377965855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3486498673812731674575613 1307437002679774377965855)
          ·
            refine ⟨1961155504019661566948783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307437002679774377965855 1961155504019661566948783)
            ·
              refine ⟨2941733256029492350423175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961155504019661566948783 2941733256029492350423175)
              ·
                refine ⟨4412599884044238525634763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941733256029492350423175 4412599884044238525634763)
                ·
                  refine ⟨6618899826066357788452145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412599884044238525634763 6618899826066357788452145)
                  ·
                    refine ⟨4964174869549768341339109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618899826066357788452145 4964174869549768341339109)
                    ·
                      refine ⟨930782788040581564001083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4964174869549768341339109 930782788040581564001083)
                      ·
                        rfl

theorem cell23_1812693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1812693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812693 prefixEnd_1812693 := by exact prefixLift 1812693
  have htrace : WordTrace (prefixWord ++ tailWord_1812693) baseStart_1812693 baseEnd_1812693 := by
    simpa [prefixWord, tailWord_1812693, baseEnd_1812693] using wordTrace_append hprefix tailTrace_1812693
  have hstable : (prefixWord ++ tailWord_1812693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812693).length < 2 ^ (prefixWord ++ tailWord_1812693).sum := by decide
  have hdescent : baseEnd_1812693 < baseStart_1812693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812696 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1812696 : Nat := 118140960795 + 1812696 * 2 ^ 59
def prefixEnd_1812696 : Nat := 4983230072969 + 3 ^ 40 * 1812696 * 2
def baseEnd_1812696 : Nat := 930784328482545052263569

theorem tailTrace_1812696 : CollatzResearch.WordTrace tailWord_1812696 prefixEnd_1812696 930784328482545052263569 := by
  unfold tailWord_1812696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057227320459725337340971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44076303093946300449787961 33057227320459725337340971)
  ·
    refine ⟨49585840980689588006011457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33057227320459725337340971 49585840980689588006011457)
    ·
      refine ⟨37189380735517191004508593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49585840980689588006011457 37189380735517191004508593)
      ·
        refine ⟨27892035551637893253381445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37189380735517191004508593 27892035551637893253381445)
        ·
          refine ⟨5229756665932104985009021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27892035551637893253381445 5229756665932104985009021)
          ·
            refine ⟨1961158749724539369378383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5229756665932104985009021 1961158749724539369378383)
            ·
              refine ⟨2941738124586809054067575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961158749724539369378383 2941738124586809054067575)
              ·
                refine ⟨4412607186880213581101363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941738124586809054067575 4412607186880213581101363)
                ·
                  refine ⟨6618910780320320371652045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412607186880213581101363 6618910780320320371652045)
                  ·
                    refine ⟨2482091542620120139369517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6618910780320320371652045 2482091542620120139369517)
                    ·
                      refine ⟨930784328482545052263569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482091542620120139369517 930784328482545052263569)
                      ·
                        rfl

theorem cell23_1812696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1812696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812696 prefixEnd_1812696 := by exact prefixLift 1812696
  have htrace : WordTrace (prefixWord ++ tailWord_1812696) baseStart_1812696 baseEnd_1812696 := by
    simpa [prefixWord, tailWord_1812696, baseEnd_1812696] using wordTrace_append hprefix tailTrace_1812696
  have hstable : (prefixWord ++ tailWord_1812696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812696).length < 2 ^ (prefixWord ++ tailWord_1812696).sum := by decide
  have hdescent : baseEnd_1812696 < baseStart_1812696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812700 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1812700 : Nat := 118140960795 + 1812700 * 2 ^ 59
def prefixEnd_1812700 : Nat := 4983230072969 + 3 ^ 40 * 1812700 * 2
def baseEnd_1812700 : Nat := 930786382405163036613551

theorem tailTrace_1812700 : CollatzResearch.WordTrace tailWord_1812700 prefixEnd_1812700 930786382405163036613551 := by
  unfold tailWord_1812700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057300266452479678913777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44076400355269972905218369 33057300266452479678913777)
  ·
    refine ⟨24792975199839359759185333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33057300266452479678913777 24792975199839359759185333)
    ·
      refine ⟨2324341424984939977423625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24792975199839359759185333 2324341424984939977423625)
      ·
        refine ⟨1743256068738704983067719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2324341424984939977423625 1743256068738704983067719)
        ·
          refine ⟨2614884103108057474601579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743256068738704983067719 2614884103108057474601579)
          ·
            refine ⟨3922326154662086211902369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614884103108057474601579 3922326154662086211902369)
            ·
              refine ⟨2941744615996564658926777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922326154662086211902369 2941744615996564658926777)
              ·
                refine ⟨2206308461997423494195083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941744615996564658926777 2206308461997423494195083)
                ·
                  refine ⟨3309462692996135241292625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206308461997423494195083 3309462692996135241292625)
                  ·
                    refine ⟨2482097019747101430969469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3309462692996135241292625 2482097019747101430969469)
                    ·
                      refine ⟨930786382405163036613551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482097019747101430969469 930786382405163036613551)
                      ·
                        rfl

theorem cell23_1812700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1812700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812700 prefixEnd_1812700 := by exact prefixLift 1812700
  have htrace : WordTrace (prefixWord ++ tailWord_1812700) baseStart_1812700 baseEnd_1812700 := by
    simpa [prefixWord, tailWord_1812700, baseEnd_1812700] using wordTrace_append hprefix tailTrace_1812700
  have hstable : (prefixWord ++ tailWord_1812700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812700).length < 2 ^ (prefixWord ++ tailWord_1812700).sum := by decide
  have hdescent : baseEnd_1812700 < baseStart_1812700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812736 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2]
def baseStart_1812736 : Nat := 118140960795 + 1812736 * 2 ^ 59
def prefixEnd_1812736 : Nat := 4983230072969 + 3 ^ 40 * 1812736 * 2
def baseEnd_1812736 : Nat := 930804867708724895763385

theorem tailTrace_1812736 : CollatzResearch.WordTrace tailWord_1812736 prefixEnd_1812736 930804867708724895763385 := by
  unfold tailWord_1812736
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057956780387268753069031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44077275707183025004092041 33057956780387268753069031)
  ·
    refine ⟨49586935170580903129603547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33057956780387268753069031 49586935170580903129603547)
    ·
      refine ⟨74380402755871354694405321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49586935170580903129603547 74380402755871354694405321)
      ·
        refine ⟨55785302066903516020803991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74380402755871354694405321 55785302066903516020803991)
        ·
          refine ⟨83677953100355274031205987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55785302066903516020803991 83677953100355274031205987)
          ·
            refine ⟨125516929650532911046808981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83677953100355274031205987 125516929650532911046808981)
            ·
              refine ⟨5883606077368730205319171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125516929650532911046808981 5883606077368730205319171)
              ·
                refine ⟨8825409116053095307978757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883606077368730205319171 8825409116053095307978757)
                ·
                  refine ⟨1654764209259955370246017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8825409116053095307978757 1654764209259955370246017)
                  ·
                    refine ⟨1241073156944966527684513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654764209259955370246017 1241073156944966527684513)
                    ·
                      refine ⟨930804867708724895763385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241073156944966527684513 930804867708724895763385)
                      ·
                        rfl

theorem cell23_1812736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_1812736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812736 prefixEnd_1812736 := by exact prefixLift 1812736
  have htrace : WordTrace (prefixWord ++ tailWord_1812736) baseStart_1812736 baseEnd_1812736 := by
    simpa [prefixWord, tailWord_1812736, baseEnd_1812736] using wordTrace_append hprefix tailTrace_1812736
  have hstable : (prefixWord ++ tailWord_1812736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812736).length < 2 ^ (prefixWord ++ tailWord_1812736).sum := by decide
  have hdescent : baseEnd_1812736 < baseStart_1812736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812753 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_1812753 : Nat := 118140960795 + 1812753 * 2 ^ 59
def prefixEnd_1812753 : Nat := 4983230072969 + 3 ^ 40 * 1812753 * 2
def baseEnd_1812753 : Nat := 930813596879851329250807

theorem tailTrace_1812753 : CollatzResearch.WordTrace tailWord_1812753 prefixEnd_1812753 930813596879851329250807 := by
  unfold tailWord_1812753
  simp only [CollatzResearch.WordTrace]
  refine ⟨66116533601712949409506913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44077689067808632939671275 66116533601712949409506913)
  ·
    refine ⟨49587400201284712057130185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66116533601712949409506913 49587400201284712057130185)
    ·
      refine ⟨37190550150963534042847639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49587400201284712057130185 37190550150963534042847639)
      ·
        refine ⟨55785825226445301064271459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37190550150963534042847639 55785825226445301064271459)
        ·
          refine ⟨83678737839667951596407189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55785825226445301064271459 83678737839667951596407189)
          ·
            refine ⟨3922440836234435231081587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83678737839667951596407189 3922440836234435231081587)
            ·
              refine ⟨5883661254351652846622381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922440836234435231081587 5883661254351652846622381)
              ·
                refine ⟨2206372970381869817483393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5883661254351652846622381 2206372970381869817483393)
                ·
                  refine ⟨1654779727786402363112545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206372970381869817483393 1654779727786402363112545)
                  ·
                    refine ⟨1241084795839801772334409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654779727786402363112545 1241084795839801772334409)
                    ·
                      refine ⟨930813596879851329250807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241084795839801772334409 930813596879851329250807)
                      ·
                        rfl

theorem cell23_1812753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_1812753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812753 prefixEnd_1812753 := by exact prefixLift 1812753
  have htrace : WordTrace (prefixWord ++ tailWord_1812753) baseStart_1812753 baseEnd_1812753 := by
    simpa [prefixWord, tailWord_1812753, baseEnd_1812753] using wordTrace_append hprefix tailTrace_1812753
  have hstable : (prefixWord ++ tailWord_1812753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812753).length < 2 ^ (prefixWord ++ tailWord_1812753).sum := by decide
  have hdescent : baseEnd_1812753 < baseStart_1812753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812789 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1812789 : Nat := 118140960795 + 1812789 * 2 ^ 59
def prefixEnd_1812789 : Nat := 4983230072969 + 3 ^ 40 * 1812789 * 2
def baseEnd_1812789 : Nat := 310277360727804396133547

theorem tailTrace_1812789 : CollatzResearch.WordTrace tailWord_1812789 prefixEnd_1812789 310277360727804396133547 := by
  unfold tailWord_1812789
  simp only [CollatzResearch.WordTrace]
  refine ⟨66117846629582527557817421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44078564419721685038544947 66117846629582527557817421)
  ·
    refine ⟨24794192486093447834181533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66117846629582527557817421 24794192486093447834181533)
    ·
      refine ⟨9297822182285042937818075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24794192486093447834181533 9297822182285042937818075)
      ·
        refine ⟨13946733273427564406727113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9297822182285042937818075 13946733273427564406727113)
        ·
          refine ⟨10460049955070673305045335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13946733273427564406727113 10460049955070673305045335)
          ·
            refine ⟨15690074932606009957568003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460049955070673305045335 15690074932606009957568003)
            ·
              refine ⟨23535112398909014936352005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15690074932606009957568003 23535112398909014936352005)
              ·
                refine ⟨4412833574795440300566001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23535112398909014936352005 4412833574795440300566001)
                ·
                  refine ⟨3309625181096580225424501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412833574795440300566001 3309625181096580225424501)
                  ·
                    refine ⟨310277360727804396133547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3309625181096580225424501 310277360727804396133547)
                    ·
                      rfl

theorem cell23_1812789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1812789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812789 prefixEnd_1812789 := by exact prefixLift 1812789
  have htrace : WordTrace (prefixWord ++ tailWord_1812789) baseStart_1812789 baseEnd_1812789 := by
    simpa [prefixWord, tailWord_1812789, baseEnd_1812789] using wordTrace_append hprefix tailTrace_1812789
  have hstable : (prefixWord ++ tailWord_1812789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812789).length < 2 ^ (prefixWord ++ tailWord_1812789).sum := by decide
  have hdescent : baseEnd_1812789 < baseStart_1812789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812793 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 5]
def baseStart_1812793 : Nat := 118140960795 + 1812793 * 2 ^ 59
def prefixEnd_1812793 : Nat := 4983230072969 + 3 ^ 40 * 1812793 * 2
def baseEnd_1812793 : Nat := 103426015122892352527847

theorem tailTrace_1812793 : CollatzResearch.WordTrace tailWord_1812793 prefixEnd_1812793 103426015122892352527847 := by
  unfold tailWord_1812793
  simp only [CollatzResearch.WordTrace]
  refine ⟨66117992521568036240963033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44078661681045357493975355 66117992521568036240963033)
  ·
    refine ⟨49588494391176027180722275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66117992521568036240963033 49588494391176027180722275)
    ·
      refine ⟨74382741586764040771083413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49588494391176027180722275 74382741586764040771083413)
      ·
        refine ⟨3486691011879564411144535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74382741586764040771083413 3486691011879564411144535)
        ·
          refine ⟨5230036517819346616716803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486691011879564411144535 5230036517819346616716803)
          ·
            refine ⟨7845054776729019925075205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230036517819346616716803 7845054776729019925075205)
            ·
              refine ⟨1470947770636691235951601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7845054776729019925075205 1470947770636691235951601)
              ·
                refine ⟨1103210827977518426963701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470947770636691235951601 1103210827977518426963701)
                ·
                  refine ⟨103426015122892352527847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1103210827977518426963701 103426015122892352527847)
                  ·
                    rfl

theorem cell23_1812793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 5].length) (baseStart_1812793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812793 prefixEnd_1812793 := by exact prefixLift 1812793
  have htrace : WordTrace (prefixWord ++ tailWord_1812793) baseStart_1812793 baseEnd_1812793 := by
    simpa [prefixWord, tailWord_1812793, baseEnd_1812793] using wordTrace_append hprefix tailTrace_1812793
  have hstable : (prefixWord ++ tailWord_1812793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812793).length < 2 ^ (prefixWord ++ tailWord_1812793).sum := by decide
  have hdescent : baseEnd_1812793 < baseStart_1812793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812839 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1812839 : Nat := 118140960795 + 1812839 * 2 ^ 59
def prefixEnd_1812839 : Nat := 4983230072969 + 3 ^ 40 * 1812839 * 2
def baseEnd_1812839 : Nat := 930857756216137992775411

theorem tailTrace_1812839 : CollatzResearch.WordTrace tailWord_1812839 prefixEnd_1812839 930857756216137992775411 := by
  unfold tailWord_1812839
  simp only [CollatzResearch.WordTrace]
  refine ⟨66119670279401386097137571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44079780186267590731425047 66119670279401386097137571)
  ·
    refine ⟨99179505419102079145706357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66119670279401386097137571 99179505419102079145706357)
    ·
      refine ⟨9298078633040819919909971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99179505419102079145706357 9298078633040819919909971)
      ·
        refine ⟨13947117949561229879864957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9298078633040819919909971 13947117949561229879864957)
        ·
          refine ⟨5230169231085461204949359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13947117949561229879864957 5230169231085461204949359)
          ·
            refine ⟨7845253846628191807424039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230169231085461204949359 7845253846628191807424039)
            ·
              refine ⟨11767880769942287711136059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845253846628191807424039 11767880769942287711136059)
              ·
                refine ⟨17651821154913431566704089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11767880769942287711136059 17651821154913431566704089)
                ·
                  refine ⟨13238865866185073675028067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17651821154913431566704089 13238865866185073675028067)
                  ·
                    refine ⟨19858298799277610512542101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13238865866185073675028067 19858298799277610512542101)
                    ·
                      refine ⟨930857756216137992775411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19858298799277610512542101 930857756216137992775411)
                      ·
                        rfl

theorem cell23_1812839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1812839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812839 prefixEnd_1812839 := by exact prefixLift 1812839
  have htrace : WordTrace (prefixWord ++ tailWord_1812839) baseStart_1812839 baseEnd_1812839 := by
    simpa [prefixWord, tailWord_1812839, baseEnd_1812839] using wordTrace_append hprefix tailTrace_1812839
  have hstable : (prefixWord ++ tailWord_1812839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812839).length < 2 ^ (prefixWord ++ tailWord_1812839).sum := by decide
  have hdescent : baseEnd_1812839 < baseStart_1812839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812853 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1812853 : Nat := 118140960795 + 1812853 * 2 ^ 59
def prefixEnd_1812853 : Nat := 4983230072969 + 3 ^ 40 * 1812853 * 2
def baseEnd_1812853 : Nat := 310288314981766979333449

theorem tailTrace_1812853 : CollatzResearch.WordTrace tailWord_1812853 prefixEnd_1812853 310288314981766979333449 := by
  unfold tailWord_1812853
  simp only [CollatzResearch.WordTrace]
  refine ⟨66120180901350666488147213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44080120600900444325431475 66120180901350666488147213)
  ·
    refine ⟨24795067838006499933055205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66120180901350666488147213 24795067838006499933055205)
    ·
      refine ⟨4649075219626218737447851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24795067838006499933055205 4649075219626218737447851)
      ·
        refine ⟨6973612829439328106171777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649075219626218737447851 6973612829439328106171777)
        ·
          refine ⟨5230209622079496079628833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6973612829439328106171777 5230209622079496079628833)
          ·
            refine ⟨3922657216559622059721625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230209622079496079628833 3922657216559622059721625)
            ·
              refine ⟨2941992912419716544791219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922657216559622059721625 2941992912419716544791219)
              ·
                refine ⟨4412989368629574817186829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941992912419716544791219 4412989368629574817186829)
                ·
                  refine ⟨1654871013236090556445061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4412989368629574817186829 1654871013236090556445061)
                  ·
                    refine ⟨310288314981766979333449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1654871013236090556445061 310288314981766979333449)
                    ·
                      rfl

theorem cell23_1812853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1812853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812853 prefixEnd_1812853 := by exact prefixLift 1812853
  have htrace : WordTrace (prefixWord ++ tailWord_1812853) baseStart_1812853 baseEnd_1812853 := by
    simpa [prefixWord, tailWord_1812853, baseEnd_1812853] using wordTrace_append hprefix tailTrace_1812853
  have hstable : (prefixWord ++ tailWord_1812853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812853).length < 2 ^ (prefixWord ++ tailWord_1812853).sum := by decide
  have hdescent : baseEnd_1812853 < baseStart_1812853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812896 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_1812896 : Nat := 118140960795 + 1812896 * 2 ^ 59
def prefixEnd_1812896 : Nat := 4983230072969 + 3 ^ 40 * 1812896 * 2
def baseEnd_1812896 : Nat := 310295674871148089920883

theorem tailTrace_1812896 : CollatzResearch.WordTrace tailWord_1812896 prefixEnd_1812896 310295674871148089920883 := by
  unfold tailWord_1812896
  simp only [CollatzResearch.WordTrace]
  refine ⟨33060874620097442415981271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44081166160129923221308361 33060874620097442415981271)
  ·
    refine ⟨49591311930146163623971907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33060874620097442415981271 49591311930146163623971907)
    ·
      refine ⟨74386967895219245435957861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49591311930146163623971907 74386967895219245435957861)
      ·
        refine ⟨13947556480353608519242099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74386967895219245435957861 13947556480353608519242099)
        ·
          refine ⟨20921334720530412778863149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13947556480353608519242099 20921334720530412778863149)
          ·
            refine ⟨7845500520198904792073681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20921334720530412778863149 7845500520198904792073681)
            ·
              refine ⟨5884125390149178594055261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845500520198904792073681 5884125390149178594055261)
              ·
                refine ⟨2206547021305941972770723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5884125390149178594055261 2206547021305941972770723)
                ·
                  refine ⟨3309820531958912959156085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206547021305941972770723 3309820531958912959156085)
                  ·
                    refine ⟨310295674871148089920883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3309820531958912959156085 310295674871148089920883)
                    ·
                      rfl

theorem cell23_1812896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_1812896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812896 prefixEnd_1812896 := by exact prefixLift 1812896
  have htrace : WordTrace (prefixWord ++ tailWord_1812896) baseStart_1812896 baseEnd_1812896 := by
    simpa [prefixWord, tailWord_1812896, baseEnd_1812896] using wordTrace_append hprefix tailTrace_1812896
  have hstable : (prefixWord ++ tailWord_1812896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812896).length < 2 ^ (prefixWord ++ tailWord_1812896).sum := by decide
  have hdescent : baseEnd_1812896 < baseStart_1812896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812903 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1812903 : Nat := 118140960795 + 1812903 * 2 ^ 59
def prefixEnd_1812903 : Nat := 4983230072969 + 3 ^ 40 * 1812903 * 2
def baseEnd_1812903 : Nat := 930890618978025742375117

theorem tailTrace_1812903 : CollatzResearch.WordTrace tailWord_1812903 prefixEnd_1812903 930890618978025742375117 := by
  unfold tailWord_1812903
  simp only [CollatzResearch.WordTrace]
  refine ⟨66122004551169525027467363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44081336367446350018311575 66122004551169525027467363)
  ·
    refine ⟨99183006826754287541201045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66122004551169525027467363 99183006826754287541201045)
    ·
      refine ⟨4649203445004107228493799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99183006826754287541201045 4649203445004107228493799)
      ·
        refine ⟨6973805167506160842740699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649203445004107228493799 6973805167506160842740699)
        ·
          refine ⟨10460707751259241264111049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6973805167506160842740699 10460707751259241264111049)
          ·
            refine ⟨7845530813444430948083287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460707751259241264111049 7845530813444430948083287)
            ·
              refine ⟨11768296220166646422124931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845530813444430948083287 11768296220166646422124931)
              ·
                refine ⟨17652444330249969633187397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768296220166646422124931 17652444330249969633187397)
                ·
                  refine ⟨3309833311921869306222637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17652444330249969633187397 3309833311921869306222637)
                  ·
                    refine ⟨1241187491970700989833489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3309833311921869306222637 1241187491970700989833489)
                    ·
                      refine ⟨930890618978025742375117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241187491970700989833489 930890618978025742375117)
                      ·
                        rfl

theorem cell23_1812903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1812903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812903 prefixEnd_1812903 := by exact prefixLift 1812903
  have htrace : WordTrace (prefixWord ++ tailWord_1812903) baseStart_1812903 baseEnd_1812903 := by
    simpa [prefixWord, tailWord_1812903, baseEnd_1812903] using wordTrace_append hprefix tailTrace_1812903
  have hstable : (prefixWord ++ tailWord_1812903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812903).length < 2 ^ (prefixWord ++ tailWord_1812903).sum := by decide
  have hdescent : baseEnd_1812903 < baseStart_1812903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812967 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1812967 : Nat := 118140960795 + 1812967 * 2 ^ 59
def prefixEnd_1812967 : Nat := 4983230072969 + 3 ^ 40 * 1812967 * 2
def baseEnd_1812967 : Nat := 930923481739913491974823

theorem tailTrace_1812967 : CollatzResearch.WordTrace tailWord_1812967 prefixEnd_1812967 930923481739913491974823 := by
  unfold tailWord_1812967
  simp only [CollatzResearch.WordTrace]
  refine ⟨66124338822937663957797155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44082892548625109305198103 66124338822937663957797155)
  ·
    refine ⟨99186508234406495936695733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66124338822937663957797155 99186508234406495936695733)
    ·
      refine ⟨9298735146975608994065225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99186508234406495936695733 9298735146975608994065225)
      ·
        refine ⟨6974051360231706745548919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9298735146975608994065225 6974051360231706745548919)
        ·
          refine ⟨10461077040347560118323379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974051360231706745548919 10461077040347560118323379)
          ·
            refine ⟨15691615560521340177485069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461077040347560118323379 15691615560521340177485069)
            ·
              refine ⟨5884355835195502566556901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15691615560521340177485069 5884355835195502566556901)
              ·
                refine ⟨1103316719099156731229419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5884355835195502566556901 1103316719099156731229419)
                ·
                  refine ⟨1654975078648735096844129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103316719099156731229419 1654975078648735096844129)
                  ·
                    refine ⟨1241231308986551322633097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1654975078648735096844129 1241231308986551322633097)
                    ·
                      refine ⟨930923481739913491974823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241231308986551322633097 930923481739913491974823)
                      ·
                        rfl

theorem cell23_1812967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1812967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812967 prefixEnd_1812967 := by exact prefixLift 1812967
  have htrace : WordTrace (prefixWord ++ tailWord_1812967) baseStart_1812967 baseEnd_1812967 := by
    simpa [prefixWord, tailWord_1812967, baseEnd_1812967] using wordTrace_append hprefix tailTrace_1812967
  have hstable : (prefixWord ++ tailWord_1812967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812967).length < 2 ^ (prefixWord ++ tailWord_1812967).sum := by decide
  have hdescent : baseEnd_1812967 < baseStart_1812967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1812973 : List Nat := [1, 5, 1, 3, 1, 3, 1, 8]
def baseStart_1812973 : Nat := 118140960795 + 1812973 * 2 ^ 59
def prefixEnd_1812973 : Nat := 4983230072969 + 3 ^ 40 * 1812973 * 2
def baseEnd_1812973 : Nat := 34478761578660758092585

theorem tailTrace_1812973 : CollatzResearch.WordTrace tailWord_1812973 prefixEnd_1812973 34478761578660758092585 := by
  unfold tailWord_1812973
  simp only [CollatzResearch.WordTrace]
  refine ⟨66124557660915926982515573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44083038440610617988343715 66124557660915926982515573)
  ·
    refine ⟨6199177280710868154610835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66124557660915926982515573 6199177280710868154610835)
    ·
      refine ⟨9298765921066302231916253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199177280710868154610835 9298765921066302231916253)
      ·
        refine ⟨3487037220399863336968595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9298765921066302231916253 3487037220399863336968595)
        ·
          refine ⟨5230555830599795005452893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487037220399863336968595 5230555830599795005452893)
          ·
            refine ⟨1961458436474923127044835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5230555830599795005452893 1961458436474923127044835)
            ·
              refine ⟨2942187654712384690567253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961458436474923127044835 2942187654712384690567253)
              ·
                refine ⟨34478761578660758092585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2942187654712384690567253 34478761578660758092585)
                ·
                  rfl

theorem cell23_1812973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 8].length) (baseStart_1812973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1812973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1812973 prefixEnd_1812973 := by exact prefixLift 1812973
  have htrace : WordTrace (prefixWord ++ tailWord_1812973) baseStart_1812973 baseEnd_1812973 := by
    simpa [prefixWord, tailWord_1812973, baseEnd_1812973] using wordTrace_append hprefix tailTrace_1812973
  have hstable : (prefixWord ++ tailWord_1812973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1812973).length < 2 ^ (prefixWord ++ tailWord_1812973).sum := by decide
  have hdescent : baseEnd_1812973 < baseStart_1812973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1812973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813016 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_1813016 : Nat := 118140960795 + 1813016 * 2 ^ 59
def prefixEnd_1813016 : Nat := 4983230072969 + 3 ^ 40 * 1813016 * 2
def baseEnd_1813016 : Nat := 310316214097327933420699

theorem tailTrace_1813016 : CollatzResearch.WordTrace tailWord_1813016 prefixEnd_1813016 310316214097327933420699 := by
  unfold tailWord_1813016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33063062999880072663165451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44084083999840096884220601 33063062999880072663165451)
  ·
    refine ⟨49594594499820108994748177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33063062999880072663165451 49594594499820108994748177)
    ·
      refine ⟨37195945874865081746061133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49594594499820108994748177 37195945874865081746061133)
      ·
        refine ⟨13948479703074405654772925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37195945874865081746061133 13948479703074405654772925)
        ·
          refine ⟨5230679888652902120539847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13948479703074405654772925 5230679888652902120539847)
          ·
            refine ⟨7846019832979353180809771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230679888652902120539847 7846019832979353180809771)
            ·
              refine ⟨11769029749469029771214657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846019832979353180809771 11769029749469029771214657)
              ·
                refine ⟨8826772312101772328410993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11769029749469029771214657 8826772312101772328410993)
                ·
                  refine ⟨6620079234076329246308245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8826772312101772328410993 6620079234076329246308245)
                  ·
                    refine ⟨310316214097327933420699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6620079234076329246308245 310316214097327933420699)
                    ·
                      rfl

theorem cell23_1813016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_1813016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813016 prefixEnd_1813016 := by exact prefixLift 1813016
  have htrace : WordTrace (prefixWord ++ tailWord_1813016) baseStart_1813016 baseEnd_1813016 := by
    simpa [prefixWord, tailWord_1813016, baseEnd_1813016] using wordTrace_append hprefix tailTrace_1813016
  have hstable : (prefixWord ++ tailWord_1813016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813016).length < 2 ^ (prefixWord ++ tailWord_1813016).sum := by decide
  have hdescent : baseEnd_1813016 < baseStart_1813016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813026 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1813026 : Nat := 118140960795 + 1813026 * 2 ^ 59
def prefixEnd_1813026 : Nat := 4983230072969 + 3 ^ 40 * 1813026 * 2
def baseEnd_1813026 : Nat := 930953777098528761137051

theorem tailTrace_1813026 : CollatzResearch.WordTrace tailWord_1813026 prefixEnd_1813026 930953777098528761137051 := by
  unfold tailWord_1813026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16531622682430979258548733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44084327153149278022796621 16531622682430979258548733)
  ·
    refine ⟨6199358505911617221955775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16531622682430979258548733 6199358505911617221955775)
    ·
      refine ⟨9299037758867425832933663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199358505911617221955775 9299037758867425832933663)
      ·
        refine ⟨13948556638301138749400495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9299037758867425832933663 13948556638301138749400495)
        ·
          refine ⟨20922834957451708124100743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13948556638301138749400495 20922834957451708124100743)
          ·
            refine ⟨31384252436177562186151115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20922834957451708124100743 31384252436177562186151115)
            ·
              refine ⟨47076378654266343279226673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31384252436177562186151115 47076378654266343279226673)
              ·
                refine ⟨35307283990699757459420005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47076378654266343279226673 35307283990699757459420005)
                ·
                  refine ⟨6620115748256204523641251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35307283990699757459420005 6620115748256204523641251)
                  ·
                    refine ⟨9930173622384306785461877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6620115748256204523641251 9930173622384306785461877)
                    ·
                      refine ⟨930953777098528761137051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9930173622384306785461877 930953777098528761137051)
                      ·
                        rfl

theorem cell23_1813026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1813026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813026 prefixEnd_1813026 := by exact prefixLift 1813026
  have htrace : WordTrace (prefixWord ++ tailWord_1813026) baseStart_1813026 baseEnd_1813026 := by
    simpa [prefixWord, tailWord_1813026, baseEnd_1813026] using wordTrace_append hprefix tailTrace_1813026
  have hstable : (prefixWord ++ tailWord_1813026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813026).length < 2 ^ (prefixWord ++ tailWord_1813026).sum := by decide
  have hdescent : baseEnd_1813026 < baseStart_1813026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813039 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_1813039 : Nat := 118140960795 + 1813039 * 2 ^ 59
def prefixEnd_1813039 : Nat := 4983230072969 + 3 ^ 40 * 1813039 * 2
def baseEnd_1813039 : Nat := 930960452347037210274491

theorem tailTrace_1813039 : CollatzResearch.WordTrace tailWord_1813039 prefixEnd_1813039 930960452347037210274491 := by
  unfold tailWord_1813039
  simp only [CollatzResearch.WordTrace]
  refine ⟨66126964878676820254418171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44084643252451213502945447 66126964878676820254418171)
  ·
    refine ⟨99190447318015230381627257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66126964878676820254418171 99190447318015230381627257)
    ·
      refine ⟨74392835488511422786220443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99190447318015230381627257 74392835488511422786220443)
      ·
        refine ⟨111589253232767134179330665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74392835488511422786220443 111589253232767134179330665)
        ·
          refine ⟨83691939924575350634497999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111589253232767134179330665 83691939924575350634497999)
          ·
            refine ⟨125537909886863025951746999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83691939924575350634497999 125537909886863025951746999)
            ·
              refine ⟨188306864830294538927620499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125537909886863025951746999 188306864830294538927620499)
              ·
                refine ⟨282460297245441808391430749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188306864830294538927620499 282460297245441808391430749)
                ·
                  refine ⟨105922611467040678146786531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282460297245441808391430749 105922611467040678146786531)
                  ·
                    refine ⟨158883917200561017220179797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105922611467040678146786531 158883917200561017220179797)
                    ·
                      refine ⟨930960452347037210274491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 158883917200561017220179797 930960452347037210274491)
                      ·
                        rfl

theorem cell23_1813039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_1813039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813039 prefixEnd_1813039 := by exact prefixLift 1813039
  have htrace : WordTrace (prefixWord ++ tailWord_1813039) baseStart_1813039 baseEnd_1813039 := by
    simpa [prefixWord, tailWord_1813039, baseEnd_1813039] using wordTrace_append hprefix tailTrace_1813039
  have hstable : (prefixWord ++ tailWord_1813039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813039).length < 2 ^ (prefixWord ++ tailWord_1813039).sum := by decide
  have hdescent : baseEnd_1813039 < baseStart_1813039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813040 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2]
def baseStart_1813040 : Nat := 118140960795 + 1813040 * 2 ^ 59
def prefixEnd_1813040 : Nat := 4983230072969 + 3 ^ 40 * 1813040 * 2
def baseEnd_1813040 : Nat := 930960965827691706361987

theorem tailTrace_1813040 : CollatzResearch.WordTrace tailWord_1813040 prefixEnd_1813040 930960965827691706361987 := by
  unfold tailWord_1813040
  simp only [CollatzResearch.WordTrace]
  refine ⟨33063500675836598712602287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44084667567782131616803049 33063500675836598712602287)
  ·
    refine ⟨49595251013754898068903431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33063500675836598712602287 49595251013754898068903431)
    ·
      refine ⟨74392876520632347103355147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49595251013754898068903431 74392876520632347103355147)
      ·
        refine ⟨111589314780948520655032721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74392876520632347103355147 111589314780948520655032721)
        ·
          refine ⟨83691986085711390491274541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111589314780948520655032721 83691986085711390491274541)
          ·
            refine ⟨31384494782141771434227953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83691986085711390491274541 31384494782141771434227953)
            ·
              refine ⟨23538371086606328575670965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31384494782141771434227953 23538371086606328575670965)
              ·
                refine ⟨2206722289369343303969153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23538371086606328575670965 2206722289369343303969153)
                ·
                  refine ⟨1655041717027007477976865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2206722289369343303969153 1655041717027007477976865)
                  ·
                    refine ⟨1241281287770255608482649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655041717027007477976865 1241281287770255608482649)
                    ·
                      refine ⟨930960965827691706361987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241281287770255608482649 930960965827691706361987)
                      ·
                        rfl

theorem cell23_1813040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2].length) (baseStart_1813040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813040 prefixEnd_1813040 := by exact prefixLift 1813040
  have htrace : WordTrace (prefixWord ++ tailWord_1813040) baseStart_1813040 baseEnd_1813040 := by
    simpa [prefixWord, tailWord_1813040, baseEnd_1813040] using wordTrace_append hprefix tailTrace_1813040
  have hstable : (prefixWord ++ tailWord_1813040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813040).length < 2 ^ (prefixWord ++ tailWord_1813040).sum := by decide
  have hdescent : baseEnd_1813040 < baseStart_1813040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813056 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1813056 : Nat := 118140960795 + 1813056 * 2 ^ 59
def prefixEnd_1813056 : Nat := 4983230072969 + 3 ^ 40 * 1813056 * 2
def baseEnd_1813056 : Nat := 930969181518163643761913

theorem tailTrace_1813056 : CollatzResearch.WordTrace tailWord_1813056 prefixEnd_1813056 930969181518163643761913 := by
  unfold tailWord_1813056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33063792459807616078893511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44085056613076821438524681 33063792459807616078893511)
  ·
    refine ⟨49595688689711424118340267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33063792459807616078893511 49595688689711424118340267)
    ·
      refine ⟨74393533034567136177510401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49595688689711424118340267 74393533034567136177510401)
      ·
        refine ⟨55795149775925352133132801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74393533034567136177510401 55795149775925352133132801)
        ·
          refine ⟨41846362331944014099849601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55795149775925352133132801 41846362331944014099849601)
          ·
            refine ⟨31384771748958010574887201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41846362331944014099849601 31384771748958010574887201)
            ·
              refine ⟨23538578811718507931165401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31384771748958010574887201 23538578811718507931165401)
              ·
                refine ⟨17653934108788880948374051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23538578811718507931165401 17653934108788880948374051)
                ·
                  refine ⟨26480901163183321422561077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17653934108788880948374051 26480901163183321422561077)
                  ·
                    refine ⟨2482584484048436383365101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26480901163183321422561077 2482584484048436383365101)
                    ·
                      refine ⟨930969181518163643761913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482584484048436383365101 930969181518163643761913)
                      ·
                        rfl

theorem cell23_1813056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1813056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813056 prefixEnd_1813056 := by exact prefixLift 1813056
  have htrace : WordTrace (prefixWord ++ tailWord_1813056) baseStart_1813056 baseEnd_1813056 := by
    simpa [prefixWord, tailWord_1813056, baseEnd_1813056] using wordTrace_append hprefix tailTrace_1813056
  have hstable : (prefixWord ++ tailWord_1813056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813056).length < 2 ^ (prefixWord ++ tailWord_1813056).sum := by decide
  have hdescent : baseEnd_1813056 < baseStart_1813056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813113 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1813113 : Nat := 118140960795 + 1813113 * 2 ^ 59
def prefixEnd_1813113 : Nat := 4983230072969 + 3 ^ 40 * 1813113 * 2
def baseEnd_1813113 : Nat := 930998449915469920749151

theorem tailTrace_1813113 : CollatzResearch.WordTrace tailWord_1813113 prefixEnd_1813113 930998449915469920749151 := by
  unfold tailWord_1813113
  simp only [CollatzResearch.WordTrace]
  refine ⟨66129663880408730892611993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44086442586939153928407995 66129663880408730892611993)
  ·
    refine ⟨49597247910306548169458995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66129663880408730892611993 49597247910306548169458995)
    ·
      refine ⟨74395871865459822254188493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49597247910306548169458995 74395871865459822254188493)
      ·
        refine ⟨27898451949547433345320685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74395871865459822254188493 27898451949547433345320685)
        ·
          refine ⟨10461919481080287504495257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27898451949547433345320685 10461919481080287504495257)
          ·
            refine ⟨7846439610810215628371443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10461919481080287504495257 7846439610810215628371443)
            ·
              refine ⟨11769659416215323442557165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846439610810215628371443 11769659416215323442557165)
              ·
                refine ⟨4413622281080746290958937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11769659416215323442557165 4413622281080746290958937)
                ·
                  refine ⟨3310216710810559718219203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4413622281080746290958937 3310216710810559718219203)
                  ·
                    refine ⟨4965325066215839577328805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310216710810559718219203 4965325066215839577328805)
                    ·
                      refine ⟨930998449915469920749151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4965325066215839577328805 930998449915469920749151)
                      ·
                        rfl

theorem cell23_1813113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1813113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813113 prefixEnd_1813113 := by exact prefixLift 1813113
  have htrace : WordTrace (prefixWord ++ tailWord_1813113) baseStart_1813113 baseEnd_1813113 := by
    simpa [prefixWord, tailWord_1813113, baseEnd_1813113] using wordTrace_append hprefix tailTrace_1813113
  have hstable : (prefixWord ++ tailWord_1813113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813113).length < 2 ^ (prefixWord ++ tailWord_1813113).sum := by decide
  have hdescent : baseEnd_1813113 < baseStart_1813113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813150 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1813150 : Nat := 118140960795 + 1813150 * 2 ^ 59
def prefixEnd_1813150 : Nat := 4983230072969 + 3 ^ 40 * 1813150 * 2
def baseEnd_1813150 : Nat := 931017448699686275986481

theorem tailTrace_1813150 : CollatzResearch.WordTrace tailWord_1813150 prefixEnd_1813150 931017448699686275986481 := by
  unfold tailWord_1813150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266376672659335776463613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44087342254183124141139269 8266376672659335776463613)
  ·
    refine ⟨3099891252247250916173855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8266376672659335776463613 3099891252247250916173855)
    ·
      refine ⟨4649836878370876374260783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099891252247250916173855 4649836878370876374260783)
      ·
        refine ⟨6974755317556314561391175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649836878370876374260783 6974755317556314561391175)
        ·
          refine ⟨10462132976334471842086763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974755317556314561391175 10462132976334471842086763)
          ·
            refine ⟨15693199464501707763130145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10462132976334471842086763 15693199464501707763130145)
            ·
              refine ⟨11769899598376280822347609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15693199464501707763130145 11769899598376280822347609)
              ·
                refine ⟨8827424698782210616760707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11769899598376280822347609 8827424698782210616760707)
                ·
                  refine ⟨13241137048173315925141061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827424698782210616760707 13241137048173315925141061)
                  ·
                    refine ⟨2482713196532496735963949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13241137048173315925141061 2482713196532496735963949)
                    ·
                      refine ⟨931017448699686275986481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482713196532496735963949 931017448699686275986481)
                      ·
                        rfl

theorem cell23_1813150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1813150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813150 prefixEnd_1813150 := by exact prefixLift 1813150
  have htrace : WordTrace (prefixWord ++ tailWord_1813150) baseStart_1813150 baseEnd_1813150 := by
    simpa [prefixWord, tailWord_1813150, baseEnd_1813150] using wordTrace_append hprefix tailTrace_1813150
  have hstable : (prefixWord ++ tailWord_1813150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813150).length < 2 ^ (prefixWord ++ tailWord_1813150).sum := by decide
  have hdescent : baseEnd_1813150 < baseStart_1813150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813176 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1813176 : Nat := 118140960795 + 1813176 * 2 ^ 59
def prefixEnd_1813176 : Nat := 4983230072969 + 3 ^ 40 * 1813176 * 2
def baseEnd_1813176 : Nat := 931030799196703174261361

theorem tailTrace_1813176 : CollatzResearch.WordTrace tailWord_1813176 prefixEnd_1813176 931030799196703174261361 := by
  unfold tailWord_1813176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33065980839590246326077691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44087974452786995101436921 33065980839590246326077691)
  ·
    refine ⟨49598971259385369489116537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33065980839590246326077691 49598971259385369489116537)
    ·
      refine ⟨37199228444539027116837403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49598971259385369489116537 37199228444539027116837403)
      ·
        refine ⟨55798842666808540675256105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37199228444539027116837403 55798842666808540675256105)
        ·
          refine ⟨41849132000106405506442079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55798842666808540675256105 41849132000106405506442079)
          ·
            refine ⟨62773698000159608259663119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41849132000106405506442079 62773698000159608259663119)
            ·
              refine ⟨94160547000239412389494679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62773698000159608259663119 94160547000239412389494679)
              ·
                refine ⟨141240820500359118584242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94160547000239412389494679 141240820500359118584242019)
                ·
                  refine ⟨211861230750538677876363029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141240820500359118584242019 211861230750538677876363029)
                  ·
                    refine ⟨9930995191431500525454517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 211861230750538677876363029 9930995191431500525454517)
                    ·
                      refine ⟨931030799196703174261361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9930995191431500525454517 931030799196703174261361)
                      ·
                        rfl

theorem cell23_1813176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1813176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813176 prefixEnd_1813176 := by exact prefixLift 1813176
  have htrace : WordTrace (prefixWord ++ tailWord_1813176) baseStart_1813176 baseEnd_1813176 := by
    simpa [prefixWord, tailWord_1813176, baseEnd_1813176] using wordTrace_append hprefix tailTrace_1813176
  have hstable : (prefixWord ++ tailWord_1813176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813176).length < 2 ^ (prefixWord ++ tailWord_1813176).sum := by decide
  have hdescent : baseEnd_1813176 < baseStart_1813176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813180 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1813180 : Nat := 118140960795 + 1813180 * 2 ^ 59
def prefixEnd_1813180 : Nat := 4983230072969 + 3 ^ 40 * 1813180 * 2
def baseEnd_1813180 : Nat := 931032853119321158611343

theorem tailTrace_1813180 : CollatzResearch.WordTrace tailWord_1813180 prefixEnd_1813180 931032853119321158611343 := by
  unfold tailWord_1813180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066053785583000667650497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44088071714110667556867329 33066053785583000667650497)
  ·
    refine ⟨24799540339187250500737873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33066053785583000667650497 24799540339187250500737873)
    ·
      refine ⟨18599655254390437875553405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24799540339187250500737873 18599655254390437875553405)
      ·
        refine ⟨6974870720396414203332527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18599655254390437875553405 6974870720396414203332527)
        ·
          refine ⟨10462306080594621304998791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974870720396414203332527 10462306080594621304998791)
          ·
            refine ⟨15693459120891931957498187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10462306080594621304998791 15693459120891931957498187)
            ·
              refine ⟨23540188681337897936247281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15693459120891931957498187 23540188681337897936247281)
              ·
                refine ⟨17655141511003423452185461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23540188681337897936247281 17655141511003423452185461)
                ·
                  refine ⟨1655169516656570948642387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17655141511003423452185461 1655169516656570948642387)
                  ·
                    refine ⟨2482754274984856422963581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655169516656570948642387 2482754274984856422963581)
                    ·
                      refine ⟨931032853119321158611343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482754274984856422963581 931032853119321158611343)
                      ·
                        rfl

theorem cell23_1813180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1813180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813180 prefixEnd_1813180 := by exact prefixLift 1813180
  have htrace : WordTrace (prefixWord ++ tailWord_1813180) baseStart_1813180 baseEnd_1813180 := by
    simpa [prefixWord, tailWord_1813180, baseEnd_1813180] using wordTrace_append hprefix tailTrace_1813180
  have hstable : (prefixWord ++ tailWord_1813180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813180).length < 2 ^ (prefixWord ++ tailWord_1813180).sum := by decide
  have hdescent : baseEnd_1813180 < baseStart_1813180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813220 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_1813220 : Nat := 118140960795 + 1813220 * 2 ^ 59
def prefixEnd_1813220 : Nat := 4983230072969 + 3 ^ 40 * 1813220 * 2
def baseEnd_1813220 : Nat := 931053392345501002111159

theorem tailTrace_1813220 : CollatzResearch.WordTrace tailWord_1813220 prefixEnd_1813220 931053392345501002111159 := by
  unfold tailWord_1813220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066783245510544083378557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44089044327347392111171409 33066783245510544083378557)
  ·
    refine ⟨12400043717066454031266959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33066783245510544083378557 12400043717066454031266959)
    ·
      refine ⟨18600065575599681046900439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12400043717066454031266959 18600065575599681046900439)
      ·
        refine ⟨27900098363399521570350659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18600065575599681046900439 27900098363399521570350659)
        ·
          refine ⟨41850147545099282355525989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27900098363399521570350659 41850147545099282355525989)
          ·
            refine ⟨7846902664706115441661123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41850147545099282355525989 7846902664706115441661123)
            ·
              refine ⟨11770353997059173162491685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846902664706115441661123 11770353997059173162491685)
              ·
                refine ⟨2206941374448594967967191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11770353997059173162491685 2206941374448594967967191)
                ·
                  refine ⟨3310412061672892451950787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206941374448594967967191 3310412061672892451950787)
                  ·
                    refine ⟨4965618092509338677926181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310412061672892451950787 4965618092509338677926181)
                    ·
                      refine ⟨931053392345501002111159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4965618092509338677926181 931053392345501002111159)
                      ·
                        rfl

theorem cell23_1813220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_1813220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813220 prefixEnd_1813220 := by exact prefixLift 1813220
  have htrace : WordTrace (prefixWord ++ tailWord_1813220) baseStart_1813220 baseEnd_1813220 := by
    simpa [prefixWord, tailWord_1813220, baseEnd_1813220] using wordTrace_append hprefix tailTrace_1813220
  have hstable : (prefixWord ++ tailWord_1813220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813220).length < 2 ^ (prefixWord ++ tailWord_1813220).sum := by decide
  have hdescent : baseEnd_1813220 < baseStart_1813220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813230 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1813230 : Nat := 118140960795 + 1813230 * 2 ^ 59
def prefixEnd_1813230 : Nat := 4983230072969 + 3 ^ 40 * 1813230 * 2
def baseEnd_1813230 : Nat := 310352842384015320995371

theorem tailTrace_1813230 : CollatzResearch.WordTrace tailWord_1813230 prefixEnd_1813230 310352842384015320995371 := by
  unfold tailWord_1813230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266741402623107484327643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44089287480656573249747429 8266741402623107484327643)
  ·
    refine ⟨12400112103934661226491465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8266741402623107484327643 12400112103934661226491465)
    ·
      refine ⟨9300084077950995919868599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12400112103934661226491465 9300084077950995919868599)
      ·
        refine ⟨13950126116926493879802899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300084077950995919868599 13950126116926493879802899)
        ·
          refine ⟨20925189175389740819704349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13950126116926493879802899 20925189175389740819704349)
          ·
            refine ⟨7846945940771152807389131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20925189175389740819704349 7846945940771152807389131)
            ·
              refine ⟨11770418911156729211083697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846945940771152807389131 11770418911156729211083697)
              ·
                refine ⟨8827814183367546908312773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11770418911156729211083697 8827814183367546908312773)
                ·
                  refine ⟨1655215159381415045308645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8827814183367546908312773 1655215159381415045308645)
                  ·
                    refine ⟨310352842384015320995371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1655215159381415045308645 310352842384015320995371)
                    ·
                      rfl

theorem cell23_1813230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1813230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813230 prefixEnd_1813230 := by exact prefixLift 1813230
  have htrace : WordTrace (prefixWord ++ tailWord_1813230) baseStart_1813230 baseEnd_1813230 := by
    simpa [prefixWord, tailWord_1813230, baseEnd_1813230] using wordTrace_append hprefix tailTrace_1813230
  have hstable : (prefixWord ++ tailWord_1813230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813230).length < 2 ^ (prefixWord ++ tailWord_1813230).sum := by decide
  have hdescent : baseEnd_1813230 < baseStart_1813230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813233 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1813233 : Nat := 118140960795 + 1813233 * 2 ^ 59
def prefixEnd_1813233 : Nat := 4983230072969 + 3 ^ 40 * 1813233 * 2
def baseEnd_1813233 : Nat := 931060067594009451248599

theorem tailTrace_1813233 : CollatzResearch.WordTrace tailWord_1813233 prefixEnd_1813233 931060067594009451248599 := by
  unfold tailWord_1813233
  simp only [CollatzResearch.WordTrace]
  refine ⟨66134040639973991386980353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44089360426649327591320235 66134040639973991386980353)
  ·
    refine ⟨49600530479980493540235265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66134040639973991386980353 49600530479980493540235265)
    ·
      refine ⟨37200397859985370155176449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49600530479980493540235265 37200397859985370155176449)
      ·
        refine ⟨27900298394989027616382337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37200397859985370155176449 27900298394989027616382337)
        ·
          refine ⟨20925223796241770712286753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27900298394989027616382337 20925223796241770712286753)
          ·
            refine ⟨15693917847181328034215065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20925223796241770712286753 15693917847181328034215065)
            ·
              refine ⟨11770438385385996025661299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15693917847181328034215065 11770438385385996025661299)
              ·
                refine ⟨17655657578078994038491949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11770438385385996025661299 17655657578078994038491949)
                ·
                  refine ⟨6620871591779622764434481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17655657578078994038491949 6620871591779622764434481)
                  ·
                    refine ⟨4965653693834717073325861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620871591779622764434481 4965653693834717073325861)
                    ·
                      refine ⟨931060067594009451248599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4965653693834717073325861 931060067594009451248599)
                      ·
                        rfl

theorem cell23_1813233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1813233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813233 prefixEnd_1813233 := by exact prefixLift 1813233
  have htrace : WordTrace (prefixWord ++ tailWord_1813233) baseStart_1813233 baseEnd_1813233 := by
    simpa [prefixWord, tailWord_1813233, baseEnd_1813233] using wordTrace_append hprefix tailTrace_1813233
  have hstable : (prefixWord ++ tailWord_1813233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813233).length < 2 ^ (prefixWord ++ tailWord_1813233).sum := by decide
  have hdescent : baseEnd_1813233 < baseStart_1813233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813240 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_1813240 : Nat := 118140960795 + 1813240 * 2 ^ 59
def prefixEnd_1813240 : Nat := 4983230072969 + 3 ^ 40 * 1813240 * 2
def baseEnd_1813240 : Nat := 931063661958590923861067

theorem tailTrace_1813240 : CollatzResearch.WordTrace tailWord_1813240 prefixEnd_1813240 931063661958590923861067 := by
  unfold tailWord_1813240
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067147975474315791242587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44089530633965754388323449 33067147975474315791242587)
  ·
    refine ⟨49600721963211473686863881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33067147975474315791242587 49600721963211473686863881)
    ·
      refine ⟨37200541472408605265147911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49600721963211473686863881 37200541472408605265147911)
      ·
        refine ⟨55800812208612907897721867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37200541472408605265147911 55800812208612907897721867)
        ·
          refine ⟨83701218312919361846582801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55800812208612907897721867 83701218312919361846582801)
          ·
            refine ⟨62775913734689521384937101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83701218312919361846582801 62775913734689521384937101)
            ·
              refine ⟨23540967650508570519351413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62775913734689521384937101 23540967650508570519351413)
              ·
                refine ⟨2206965717235178486189195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23540967650508570519351413 2206965717235178486189195)
                ·
                  refine ⟨3310448575852767729283793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206965717235178486189195 3310448575852767729283793)
                  ·
                    refine ⟨2482836431889575796962845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3310448575852767729283793 2482836431889575796962845)
                    ·
                      refine ⟨931063661958590923861067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482836431889575796962845 931063661958590923861067)
                      ·
                        rfl

theorem cell23_1813240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_1813240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813240 prefixEnd_1813240 := by exact prefixLift 1813240
  have htrace : WordTrace (prefixWord ++ tailWord_1813240) baseStart_1813240 baseEnd_1813240 := by
    simpa [prefixWord, tailWord_1813240, baseEnd_1813240] using wordTrace_append hprefix tailTrace_1813240
  have hstable : (prefixWord ++ tailWord_1813240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813240).length < 2 ^ (prefixWord ++ tailWord_1813240).sum := by decide
  have hdescent : baseEnd_1813240 < baseStart_1813240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813250 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1813250 : Nat := 118140960795 + 1813250 * 2 ^ 59
def prefixEnd_1813250 : Nat := 4983230072969 + 3 ^ 40 * 1813250 * 2
def baseEnd_1813250 : Nat := 931068796765135884736021

theorem tailTrace_1813250 : CollatzResearch.WordTrace tailWord_1813250 prefixEnd_1813250 931068796765135884736021 := by
  unfold tailWord_1813250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533665170228100822587301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44089773787274935526899469 16533665170228100822587301)
  ·
    refine ⟨3100062219417768904235119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16533665170228100822587301 3100062219417768904235119)
    ·
      refine ⟨4650093329126653356352679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100062219417768904235119 4650093329126653356352679)
      ·
        refine ⟨6975139993689980034529019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650093329126653356352679 6975139993689980034529019)
        ·
          refine ⟨10462709990534970051793529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6975139993689980034529019 10462709990534970051793529)
          ·
            refine ⟨7847032492901227538845147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10462709990534970051793529 7847032492901227538845147)
            ·
              refine ⟨11770548739351841308267721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847032492901227538845147 11770548739351841308267721)
              ·
                refine ⟨8827911554513880981200791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11770548739351841308267721 8827911554513880981200791)
                ·
                  refine ⟨13241867331770821471801187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827911554513880981200791 13241867331770821471801187)
                  ·
                    refine ⟨19862800997656232207701781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13241867331770821471801187 19862800997656232207701781)
                    ·
                      refine ⟨931068796765135884736021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19862800997656232207701781 931068796765135884736021)
                      ·
                        rfl

theorem cell23_1813250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1813250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813250 prefixEnd_1813250 := by exact prefixLift 1813250
  have htrace : WordTrace (prefixWord ++ tailWord_1813250) baseStart_1813250 baseEnd_1813250 := by
    simpa [prefixWord, tailWord_1813250, baseEnd_1813250] using wordTrace_append hprefix tailTrace_1813250
  have hstable : (prefixWord ++ tailWord_1813250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813250).length < 2 ^ (prefixWord ++ tailWord_1813250).sum := by decide
  have hdescent : baseEnd_1813250 < baseStart_1813250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813303 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 2, 6]
def baseStart_1813303 : Nat := 118140960795 + 1813303 * 2 ^ 59
def prefixEnd_1813303 : Nat := 4983230072969 + 3 ^ 40 * 1813303 * 2
def baseEnd_1813303 : Nat := 310365337079941392457759

theorem tailTrace_1813303 : CollatzResearch.WordTrace tailWord_1813303 prefixEnd_1813303 310365337079941392457759 := by
  unfold tailWord_1813303
  simp only [CollatzResearch.WordTrace]
  refine ⟨66136593749720393342028563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44091062499813595561352375 66136593749720393342028563)
  ·
    refine ⟨99204890624580590013042845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66136593749720393342028563 99204890624580590013042845)
    ·
      refine ⟨37201833984217721254891067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99204890624580590013042845 37201833984217721254891067)
      ·
        refine ⟨55802750976326581882336601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37201833984217721254891067 55802750976326581882336601)
        ·
          refine ⟨41852063232244936411752451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55802750976326581882336601 41852063232244936411752451)
          ·
            refine ⟨62778094848367404617628677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41852063232244936411752451 62778094848367404617628677)
            ·
              refine ⟨11770892784068888365805377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62778094848367404617628677 11770892784068888365805377)
              ·
                refine ⟨8828169588051666274354033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11770892784068888365805377 8828169588051666274354033)
                ·
                  refine ⟨6621127191038749705765525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8828169588051666274354033 6621127191038749705765525)
                  ·
                    refine ⟨310365337079941392457759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6621127191038749705765525 310365337079941392457759)
                    ·
                      rfl

theorem cell23_1813303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_1813303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813303 prefixEnd_1813303 := by exact prefixLift 1813303
  have htrace : WordTrace (prefixWord ++ tailWord_1813303) baseStart_1813303 baseEnd_1813303 := by
    simpa [prefixWord, tailWord_1813303, baseEnd_1813303] using wordTrace_append hprefix tailTrace_1813303
  have hstable : (prefixWord ++ tailWord_1813303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813303).length < 2 ^ (prefixWord ++ tailWord_1813303).sum := by decide
  have hdescent : baseEnd_1813303 < baseStart_1813303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813330 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1813330 : Nat := 118140960795 + 1813330 * 2 ^ 59
def prefixEnd_1813330 : Nat := 4983230072969 + 3 ^ 40 * 1813330 * 2
def baseEnd_1813330 : Nat := 931109875217495571735653

theorem tailTrace_1813330 : CollatzResearch.WordTrace tailWord_1813330 prefixEnd_1813330 931109875217495571735653 := by
  unfold tailWord_1813330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534394630155644238315361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44091719013748384635507629 16534394630155644238315361)
  ·
    refine ⟨12400795972616733178736521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16534394630155644238315361 12400795972616733178736521)
    ·
      refine ⟨9300596979462549884052391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12400795972616733178736521 9300596979462549884052391)
      ·
        refine ⟨13950895469193824826078587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300596979462549884052391 13950895469193824826078587)
        ·
          refine ⟨20926343203790737239117881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13950895469193824826078587 20926343203790737239117881)
          ·
            refine ⟨15694757402843052929338411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20926343203790737239117881 15694757402843052929338411)
            ·
              refine ⟨23542136104264579394007617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15694757402843052929338411 23542136104264579394007617)
              ·
                refine ⟨17656602078198434545505713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23542136104264579394007617 17656602078198434545505713)
                ·
                  refine ⟨13242451558648825909129285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17656602078198434545505713 13242451558648825909129285)
                  ·
                    refine ⟨2482959667246654857961741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13242451558648825909129285 2482959667246654857961741)
                    ·
                      refine ⟨931109875217495571735653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2482959667246654857961741 931109875217495571735653)
                      ·
                        rfl

theorem cell23_1813330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1813330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813330 prefixEnd_1813330 := by exact prefixLift 1813330
  have htrace : WordTrace (prefixWord ++ tailWord_1813330) baseStart_1813330 baseEnd_1813330 := by
    simpa [prefixWord, tailWord_1813330, baseEnd_1813330] using wordTrace_append hprefix tailTrace_1813330
  have hstable : (prefixWord ++ tailWord_1813330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813330).length < 2 ^ (prefixWord ++ tailWord_1813330).sum := by decide
  have hdescent : baseEnd_1813330 < baseStart_1813330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813360 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_1813360 : Nat := 118140960795 + 1813360 * 2 ^ 59
def prefixEnd_1813360 : Nat := 4983230072969 + 3 ^ 40 * 1813360 * 2
def baseEnd_1813360 : Nat := 931125279637130454360515

theorem tailTrace_1813360 : CollatzResearch.WordTrace tailWord_1813360 prefixEnd_1813360 931125279637130454360515 := by
  unfold tailWord_1813360
  simp only [CollatzResearch.WordTrace]
  refine ⟨33069336355256946038426767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44092448473675928051235689 33069336355256946038426767)
  ·
    refine ⟨49604004532885419057640151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33069336355256946038426767 49604004532885419057640151)
    ·
      refine ⟨74406006799328128586460227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49604004532885419057640151 74406006799328128586460227)
      ·
        refine ⟨111609010198992192879690341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74406006799328128586460227 111609010198992192879690341)
        ·
          refine ⟨20926689412311036164941939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111609010198992192879690341 20926689412311036164941939)
          ·
            refine ⟨31390034118466554247412909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20926689412311036164941939 31390034118466554247412909)
            ·
              refine ⟨11771262794424957842779841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31390034118466554247412909 11771262794424957842779841)
              ·
                refine ⟨8828447095818718382084881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11771262794424957842779841 8828447095818718382084881)
                ·
                  refine ⟨6621335321864038786563661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8828447095818718382084881 6621335321864038786563661)
                  ·
                    refine ⟨2483000745699014544961373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6621335321864038786563661 2483000745699014544961373)
                    ·
                      refine ⟨931125279637130454360515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483000745699014544961373 931125279637130454360515)
                      ·
                        rfl

theorem cell23_1813360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_1813360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813360 prefixEnd_1813360 := by exact prefixLift 1813360
  have htrace : WordTrace (prefixWord ++ tailWord_1813360) baseStart_1813360 baseEnd_1813360 := by
    simpa [prefixWord, tailWord_1813360, baseEnd_1813360] using wordTrace_append hprefix tailTrace_1813360
  have hstable : (prefixWord ++ tailWord_1813360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813360).length < 2 ^ (prefixWord ++ tailWord_1813360).sum := by decide
  have hdescent : baseEnd_1813360 < baseStart_1813360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813361 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_1813361 : Nat := 118140960795 + 1813361 * 2 ^ 59
def prefixEnd_1813361 : Nat := 4983230072969 + 3 ^ 40 * 1813361 * 2
def baseEnd_1813361 : Nat := 931125793117784950448011

theorem tailTrace_1813361 : CollatzResearch.WordTrace tailWord_1813361 prefixEnd_1813361 931125793117784950448011 := by
  unfold tailWord_1813361
  simp only [CollatzResearch.WordTrace]
  refine ⟨66138709183510269247639937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44092472789006846165093291 66138709183510269247639937)
  ·
    refine ⟨49604031887632701935729953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66138709183510269247639937 49604031887632701935729953)
    ·
      refine ⟨37203023915724526451797465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49604031887632701935729953 37203023915724526451797465)
      ·
        refine ⟨27902267936793394838848099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37203023915724526451797465 27902267936793394838848099)
        ·
          refine ⟨41853401905190092258272149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902267936793394838848099 41853401905190092258272149)
          ·
            refine ⟨1961878214305785574606507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41853401905190092258272149 1961878214305785574606507)
            ·
              refine ⟨2942817321458678361909761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961878214305785574606507 2942817321458678361909761)
              ·
                refine ⟨2207112991094008771432321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942817321458678361909761 2207112991094008771432321)
                ·
                  refine ⟨1655334743320506578574241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207112991094008771432321 1655334743320506578574241)
                  ·
                    refine ⟨1241501057490379933930681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655334743320506578574241 1241501057490379933930681)
                    ·
                      refine ⟨931125793117784950448011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241501057490379933930681 931125793117784950448011)
                      ·
                        rfl

theorem cell23_1813361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_1813361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813361 prefixEnd_1813361 := by exact prefixLift 1813361
  have htrace : WordTrace (prefixWord ++ tailWord_1813361) baseStart_1813361 baseEnd_1813361 := by
    simpa [prefixWord, tailWord_1813361, baseEnd_1813361] using wordTrace_append hprefix tailTrace_1813361
  have hstable : (prefixWord ++ tailWord_1813361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813361).length < 2 ^ (prefixWord ++ tailWord_1813361).sum := by decide
  have hdescent : baseEnd_1813361 < baseStart_1813361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813393 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_1813393 : Nat := 118140960795 + 1813393 * 2 ^ 59
def prefixEnd_1813393 : Nat := 4983230072969 + 3 ^ 40 * 1813393 * 2
def baseEnd_1813393 : Nat := 310380741499576275082621

theorem tailTrace_1813393 : CollatzResearch.WordTrace tailWord_1813393 prefixEnd_1813393 310380741499576275082621 := by
  unfold tailWord_1813393
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139876319394338712804833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44093250879596225808536555 66139876319394338712804833)
  ·
    refine ⟨49604907239545754034603625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66139876319394338712804833 49604907239545754034603625)
    ·
      refine ⟨37203680429659315525952719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49604907239545754034603625 37203680429659315525952719)
      ·
        refine ⟨55805520644488973288929079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37203680429659315525952719 55805520644488973288929079)
        ·
          refine ⟨83708280966733459933393619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55805520644488973288929079 83708280966733459933393619)
          ·
            refine ⟨125562421450100189900090429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83708280966733459933393619 125562421450100189900090429)
            ·
              refine ⟨47085908043787571212533911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125562421450100189900090429 47085908043787571212533911)
              ·
                refine ⟨70628862065681356818800867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47085908043787571212533911 70628862065681356818800867)
                ·
                  refine ⟨105943293098522035228201301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70628862065681356818800867 105943293098522035228201301)
                  ·
                    refine ⟨310380741499576275082621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 105943293098522035228201301 310380741499576275082621)
                    ·
                      rfl

theorem cell23_1813393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_1813393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813393 prefixEnd_1813393 := by exact prefixLift 1813393
  have htrace : WordTrace (prefixWord ++ tailWord_1813393) baseStart_1813393 baseEnd_1813393 := by
    simpa [prefixWord, tailWord_1813393, baseEnd_1813393] using wordTrace_append hprefix tailTrace_1813393
  have hstable : (prefixWord ++ tailWord_1813393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813393).length < 2 ^ (prefixWord ++ tailWord_1813393).sum := by decide
  have hdescent : baseEnd_1813393 < baseStart_1813393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813454 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1813454 : Nat := 118140960795 + 1813454 * 2 ^ 59
def prefixEnd_1813454 : Nat := 4983230072969 + 3 ^ 40 * 1813454 * 2
def baseEnd_1813454 : Nat := 931173546818653086585083

theorem tailTrace_1813454 : CollatzResearch.WordTrace tailWord_1813454 prefixEnd_1813454 931173546818653086585083 := by
  unfold tailWord_1813454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8267762646521668266346927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44094734114782230753850277 8267762646521668266346927)
  ·
    refine ⟨12401643969782502399520391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8267762646521668266346927 12401643969782502399520391)
    ·
      refine ⟨18602465954673753599280587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12401643969782502399520391 18602465954673753599280587)
      ·
        refine ⟨27903698932010630398920881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18602465954673753599280587 27903698932010630398920881)
        ·
          refine ⟨20927774199007972799190661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27903698932010630398920881 20927774199007972799190661)
          ·
            refine ⟨3923957662313994899848249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20927774199007972799190661 3923957662313994899848249)
            ·
              refine ⟨2942968246735496174886187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3923957662313994899848249 2942968246735496174886187)
              ·
                refine ⟨4414452370103244262329281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942968246735496174886187 4414452370103244262329281)
                ·
                  refine ⟨3310839277577433196746961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414452370103244262329281 3310839277577433196746961)
                  ·
                    refine ⟨2483129458183074897560221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3310839277577433196746961 2483129458183074897560221)
                    ·
                      refine ⟨931173546818653086585083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483129458183074897560221 931173546818653086585083)
                      ·
                        rfl

theorem cell23_1813454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1813454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813454 prefixEnd_1813454 := by exact prefixLift 1813454
  have htrace : WordTrace (prefixWord ++ tailWord_1813454) baseStart_1813454 baseEnd_1813454 := by
    simpa [prefixWord, tailWord_1813454, baseEnd_1813454] using wordTrace_append hprefix tailTrace_1813454
  have hstable : (prefixWord ++ tailWord_1813454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813454).length < 2 ^ (prefixWord ++ tailWord_1813454).sum := by decide
  have hdescent : baseEnd_1813454 < baseStart_1813454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813474 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1813474 : Nat := 118140960795 + 1813474 * 2 ^ 59
def prefixEnd_1813474 : Nat := 4983230072969 + 3 ^ 40 * 1813474 * 2
def baseEnd_1813474 : Nat := 103464868492415889814999

theorem tailTrace_1813474 : CollatzResearch.WordTrace tailWord_1813474 prefixEnd_1813474 103464868492415889814999 := by
  unfold tailWord_1813474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535707658025222386625869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44095220421400593031002317 16535707658025222386625869)
  ·
    refine ⟨6200890371759458394984701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16535707658025222386625869 6200890371759458394984701)
    ·
      refine ⟨2325333889409796898119263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6200890371759458394984701 2325333889409796898119263)
      ·
        refine ⟨3488000834114695347178895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325333889409796898119263 3488000834114695347178895)
        ·
          refine ⟨5232001251172043020768343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488000834114695347178895 5232001251172043020768343)
          ·
            refine ⟨7848001876758064531152515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232001251172043020768343 7848001876758064531152515)
            ·
              refine ⟨11772002815137096796728773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848001876758064531152515 11772002815137096796728773)
              ·
                refine ⟨2207250527838205649386645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11772002815137096796728773 2207250527838205649386645)
                ·
                  refine ⟨103464868492415889814999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2207250527838205649386645 103464868492415889814999)
                  ·
                    rfl

theorem cell23_1813474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1813474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813474 prefixEnd_1813474 := by exact prefixLift 1813474
  have htrace : WordTrace (prefixWord ++ tailWord_1813474) baseStart_1813474 baseEnd_1813474 := by
    simpa [prefixWord, tailWord_1813474, baseEnd_1813474] using wordTrace_append hprefix tailTrace_1813474
  have hstable : (prefixWord ++ tailWord_1813474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813474).length < 2 ^ (prefixWord ++ tailWord_1813474).sum := by decide
  have hdescent : baseEnd_1813474 < baseStart_1813474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813518 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1813518 : Nat := 118140960795 + 1813518 * 2 ^ 59
def prefixEnd_1813518 : Nat := 4983230072969 + 3 ^ 40 * 1813518 * 2
def baseEnd_1813518 : Nat := 931206409580540836184789

theorem tailTrace_1813518 : CollatzResearch.WordTrace tailWord_1813518 prefixEnd_1813518 931206409580540836184789 := by
  unfold tailWord_1813518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8268054430492685632638151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44096290295960990040736805 8268054430492685632638151)
  ·
    refine ⟨12402081645739028448957227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8268054430492685632638151 12402081645739028448957227)
    ·
      refine ⟨18603122468608542673435841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12402081645739028448957227 18603122468608542673435841)
      ·
        refine ⟨13952341851456407005076881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18603122468608542673435841 13952341851456407005076881)
        ·
          refine ⟨10464256388592305253807661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13952341851456407005076881 10464256388592305253807661)
          ·
            refine ⟨3924096145722114470177873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10464256388592305253807661 3924096145722114470177873)
            ·
              refine ⟨2943072109291585852633405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924096145722114470177873 2943072109291585852633405)
              ·
                refine ⟨1103652040984344694737527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2943072109291585852633405 1103652040984344694737527)
                ·
                  refine ⟨1655478061476517042106291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103652040984344694737527 1655478061476517042106291)
                  ·
                    refine ⟨2483217092214775563159437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1655478061476517042106291 2483217092214775563159437)
                    ·
                      refine ⟨931206409580540836184789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483217092214775563159437 931206409580540836184789)
                      ·
                        rfl

theorem cell23_1813518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1813518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813518 prefixEnd_1813518 := by exact prefixLift 1813518
  have htrace : WordTrace (prefixWord ++ tailWord_1813518) baseStart_1813518 baseEnd_1813518 := by
    simpa [prefixWord, tailWord_1813518, baseEnd_1813518] using wordTrace_append hprefix tailTrace_1813518
  have hstable : (prefixWord ++ tailWord_1813518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813518).length < 2 ^ (prefixWord ++ tailWord_1813518).sum := by decide
  have hdescent : baseEnd_1813518 < baseStart_1813518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813530 : List Nat := [3, 1, 1, 3, 1, 2, 12]
def baseStart_1813530 : Nat := 118140960795 + 1813530 * 2 ^ 59
def prefixEnd_1813530 : Nat := 4983230072969 + 3 ^ 40 * 1813530 * 2
def baseEnd_1813530 : Nat := 11496451498128330731293

theorem tailTrace_1813530 : CollatzResearch.WordTrace tailWord_1813530 prefixEnd_1813530 11496451498128330731293 := by
  unfold tailWord_1813530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16536218279974502777635511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44096582079932007407028029 16536218279974502777635511)
  ·
    refine ⟨24804327419961754166453267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16536218279974502777635511 24804327419961754166453267)
    ·
      refine ⟨37206491129942631249679901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24804327419961754166453267 37206491129942631249679901)
      ·
        refine ⟨13952434173728486718629963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37206491129942631249679901 13952434173728486718629963)
        ·
          refine ⟨20928651260592730077944945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13952434173728486718629963 20928651260592730077944945)
          ·
            refine ⟨15696488445444547558458709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20928651260592730077944945 15696488445444547558458709)
            ·
              refine ⟨11496451498128330731293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15696488445444547558458709 11496451498128330731293)
              ·
                rfl

theorem cell23_1813530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 12].length) (baseStart_1813530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813530 prefixEnd_1813530 := by exact prefixLift 1813530
  have htrace : WordTrace (prefixWord ++ tailWord_1813530) baseStart_1813530 baseEnd_1813530 := by
    simpa [prefixWord, tailWord_1813530, baseEnd_1813530] using wordTrace_append hprefix tailTrace_1813530
  have hstable : (prefixWord ++ tailWord_1813530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813530).length < 2 ^ (prefixWord ++ tailWord_1813530).sum := by decide
  have hdescent : baseEnd_1813530 < baseStart_1813530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813541 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_1813541 : Nat := 118140960795 + 1813541 * 2 ^ 59
def prefixEnd_1813541 : Nat := 4983230072969 + 3 ^ 40 * 1813541 * 2
def baseEnd_1813541 : Nat := 931218219635594246197183

theorem tailTrace_1813541 : CollatzResearch.WordTrace tailWord_1813541 prefixEnd_1813541 931218219635594246197183 := by
  unfold tailWord_1813541
  simp only [CollatzResearch.WordTrace]
  refine ⟨66145274322858159989192477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44096849548572106659461651 66145274322858159989192477)
  ·
    refine ⟨24804477871071809995947179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66145274322858159989192477 24804477871071809995947179)
    ·
      refine ⟨37206716806607714993920769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24804477871071809995947179 37206716806607714993920769)
      ·
        refine ⟨27905037604955786245440577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37206716806607714993920769 27905037604955786245440577)
        ·
          refine ⟨20928778203716839684080433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27905037604955786245440577 20928778203716839684080433)
          ·
            refine ⟨15696583652787629763060325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20928778203716839684080433 15696583652787629763060325)
            ·
              refine ⟨2943109434897680580573811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15696583652787629763060325 2943109434897680580573811)
              ·
                refine ⟨4414664152346520870860717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943109434897680580573811 4414664152346520870860717)
                ·
                  refine ⟨1655499057129945326572769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4414664152346520870860717 1655499057129945326572769)
                  ·
                    refine ⟨1241624292847458994929577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655499057129945326572769 1241624292847458994929577)
                    ·
                      refine ⟨931218219635594246197183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241624292847458994929577 931218219635594246197183)
                      ·
                        rfl

theorem cell23_1813541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_1813541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813541 prefixEnd_1813541 := by exact prefixLift 1813541
  have htrace : WordTrace (prefixWord ++ tailWord_1813541) baseStart_1813541 baseEnd_1813541 := by
    simpa [prefixWord, tailWord_1813541, baseEnd_1813541] using wordTrace_append hprefix tailTrace_1813541
  have hstable : (prefixWord ++ tailWord_1813541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813541).length < 2 ^ (prefixWord ++ tailWord_1813541).sum := by decide
  have hdescent : baseEnd_1813541 < baseStart_1813541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813558 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_1813558 : Nat := 118140960795 + 1813558 * 2 ^ 59
def prefixEnd_1813558 : Nat := 4983230072969 + 3 ^ 40 * 1813558 * 2
def baseEnd_1813558 : Nat := 931226948806720679684605

theorem tailTrace_1813558 : CollatzResearch.WordTrace tailWord_1813558 prefixEnd_1813558 931226948806720679684605 := by
  unfold tailWord_1813558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134118397737285743285083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44097262909197714595040885 4134118397737285743285083)
  ·
    refine ⟨6201177596605928614927625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4134118397737285743285083 6201177596605928614927625)
    ·
      refine ⟨4650883197454446461195719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6201177596605928614927625 4650883197454446461195719)
      ·
        refine ⟨6976324796181669691793579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650883197454446461195719 6976324796181669691793579)
        ·
          refine ⟨10464487194272504537690369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976324796181669691793579 10464487194272504537690369)
          ·
            refine ⟨7848365395704378403267777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10464487194272504537690369 7848365395704378403267777)
            ·
              refine ⟨5886274046778283802450833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7848365395704378403267777 5886274046778283802450833)
              ·
                refine ⟨4414705535083712851838125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886274046778283802450833 4414705535083712851838125)
                ·
                  refine ⟨1655514575656392319439297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4414705535083712851838125 1655514575656392319439297)
                  ·
                    refine ⟨1241635931742294239579473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655514575656392319439297 1241635931742294239579473)
                    ·
                      refine ⟨931226948806720679684605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241635931742294239579473 931226948806720679684605)
                      ·
                        rfl

theorem cell23_1813558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_1813558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813558 prefixEnd_1813558 := by exact prefixLift 1813558
  have htrace : WordTrace (prefixWord ++ tailWord_1813558) baseStart_1813558 baseEnd_1813558 := by
    simpa [prefixWord, tailWord_1813558, baseEnd_1813558] using wordTrace_append hprefix tailTrace_1813558
  have hstable : (prefixWord ++ tailWord_1813558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813558).length < 2 ^ (prefixWord ++ tailWord_1813558).sum := by decide
  have hdescent : baseEnd_1813558 < baseStart_1813558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813561 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1813561 : Nat := 118140960795 + 1813561 * 2 ^ 59
def prefixEnd_1813561 : Nat := 4983230072969 + 3 ^ 40 * 1813561 * 2
def baseEnd_1813561 : Nat := 931228489248684167947091

theorem tailTrace_1813561 : CollatzResearch.WordTrace tailWord_1813561 prefixEnd_1813561 931228489248684167947091 := by
  unfold tailWord_1813561
  simp only [CollatzResearch.WordTrace]
  refine ⟨66146003782785703404920537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44097335855190468936613691 66146003782785703404920537)
  ·
    refine ⟨49609502837089277553690403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66146003782785703404920537 49609502837089277553690403)
    ·
      refine ⟨74414254255633916330535605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49609502837089277553690403 74414254255633916330535605)
      ·
        refine ⟨6976336336465679655987713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74414254255633916330535605 6976336336465679655987713)
        ·
          refine ⟨5232252252349259741990785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6976336336465679655987713 5232252252349259741990785)
          ·
            refine ⟨3924189189261944806493089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232252252349259741990785 3924189189261944806493089)
            ·
              refine ⟨2943141891946458604869817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924189189261944806493089 2943141891946458604869817)
              ·
                refine ⟨2207356418959843953652363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943141891946458604869817 2207356418959843953652363)
                ·
                  refine ⟨3311034628439765930478545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207356418959843953652363 3311034628439765930478545)
                  ·
                    refine ⟨2483275971329824447858909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3311034628439765930478545 2483275971329824447858909)
                    ·
                      refine ⟨931228489248684167947091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483275971329824447858909 931228489248684167947091)
                      ·
                        rfl

theorem cell23_1813561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1813561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813561 prefixEnd_1813561 := by exact prefixLift 1813561
  have htrace : WordTrace (prefixWord ++ tailWord_1813561) baseStart_1813561 baseEnd_1813561 := by
    simpa [prefixWord, tailWord_1813561, baseEnd_1813561] using wordTrace_append hprefix tailTrace_1813561
  have hstable : (prefixWord ++ tailWord_1813561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813561).length < 2 ^ (prefixWord ++ tailWord_1813561).sum := by decide
  have hdescent : baseEnd_1813561 < baseStart_1813561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813564 : List Nat := [2, 2, 2, 2, 2, 4, 2, 7]
def baseStart_1813564 : Nat := 118140960795 + 1813564 * 2 ^ 59
def prefixEnd_1813564 : Nat := 4983230072969 + 3 ^ 40 * 1813564 * 2
def baseEnd_1813564 : Nat := 34490001099653616896651

theorem tailTrace_1813564 : CollatzResearch.WordTrace tailWord_1813564 prefixEnd_1813564 34490001099653616896651 := by
  unfold tailWord_1813564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33073056600887417458639873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44097408801183223278186497 33073056600887417458639873)
  ·
    refine ⟨24804792450665563093979905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33073056600887417458639873 24804792450665563093979905)
    ·
      refine ⟨18603594337999172320484929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24804792450665563093979905 18603594337999172320484929)
      ·
        refine ⟨13952695753499379240363697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18603594337999172320484929 13952695753499379240363697)
        ·
          refine ⟨10464521815124534430272773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13952695753499379240363697 10464521815124534430272773)
          ·
            refine ⟨1962097840335850205676145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10464521815124534430272773 1962097840335850205676145)
            ·
              refine ⟨1471573380251887654257109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962097840335850205676145 1471573380251887654257109)
              ·
                refine ⟨34490001099653616896651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1471573380251887654257109 34490001099653616896651)
                ·
                  rfl

theorem cell23_1813564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 7].length) (baseStart_1813564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813564 prefixEnd_1813564 := by exact prefixLift 1813564
  have htrace : WordTrace (prefixWord ++ tailWord_1813564) baseStart_1813564 baseEnd_1813564 := by
    simpa [prefixWord, tailWord_1813564, baseEnd_1813564] using wordTrace_append hprefix tailTrace_1813564
  have hstable : (prefixWord ++ tailWord_1813564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813564).length < 2 ^ (prefixWord ++ tailWord_1813564).sum := by decide
  have hdescent : baseEnd_1813564 < baseStart_1813564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813575 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_1813575 : Nat := 118140960795 + 1813575 * 2 ^ 59
def prefixEnd_1813575 : Nat := 4983230072969 + 3 ^ 40 * 1813575 * 2
def baseEnd_1813575 : Nat := 931235677977847113172027

theorem tailTrace_1813575 : CollatzResearch.WordTrace tailWord_1813575 prefixEnd_1813575 931235677977847113172027 := by
  unfold tailWord_1813575
  simp only [CollatzResearch.WordTrace]
  refine ⟨66146514404734983795930179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44097676269823322530620119 66146514404734983795930179)
  ·
    refine ⟨99219771607102475693895269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66146514404734983795930179 99219771607102475693895269)
    ·
      refine ⟨18603707176331714192605363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99219771607102475693895269 18603707176331714192605363)
      ·
        refine ⟨27905560764497571288908045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18603707176331714192605363 27905560764497571288908045)
        ·
          refine ⟨10464585286686589233340517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27905560764497571288908045 10464585286686589233340517)
          ·
            refine ⟨1962109741253735481251347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10464585286686589233340517 1962109741253735481251347)
            ·
              refine ⟨2943164611880603221877021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962109741253735481251347 2943164611880603221877021)
              ·
                refine ⟨1103686729455226208203883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2943164611880603221877021 1103686729455226208203883)
                ·
                  refine ⟨1655530094182839312305825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103686729455226208203883 1655530094182839312305825)
                  ·
                    refine ⟨1241647570637129484229369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655530094182839312305825 1241647570637129484229369)
                    ·
                      refine ⟨931235677977847113172027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241647570637129484229369 931235677977847113172027)
                      ·
                        rfl

theorem cell23_1813575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_1813575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813575 prefixEnd_1813575 := by exact prefixLift 1813575
  have htrace : WordTrace (prefixWord ++ tailWord_1813575) baseStart_1813575 baseEnd_1813575 := by
    simpa [prefixWord, tailWord_1813575, baseEnd_1813575] using wordTrace_append hprefix tailTrace_1813575
  have hstable : (prefixWord ++ tailWord_1813575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813575).length < 2 ^ (prefixWord ++ tailWord_1813575).sum := by decide
  have hdescent : baseEnd_1813575 < baseStart_1813575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813617 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_1813617 : Nat := 118140960795 + 1813617 * 2 ^ 59
def prefixEnd_1813617 : Nat := 4983230072969 + 3 ^ 40 * 1813617 * 2
def baseEnd_1813617 : Nat := 931257244165335948846833

theorem tailTrace_1813617 : CollatzResearch.WordTrace tailWord_1813617 prefixEnd_1813617 931257244165335948846833 := by
  unfold tailWord_1813617
  simp only [CollatzResearch.WordTrace]
  refine ⟨66148046270582824968959105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44098697513721883312639403 66148046270582824968959105)
  ·
    refine ⟨49611034702937118726719329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66148046270582824968959105 49611034702937118726719329)
    ·
      refine ⟨37208276027202839045039497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49611034702937118726719329 37208276027202839045039497)
      ·
        refine ⟨27906207020402129283779623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37208276027202839045039497 27906207020402129283779623)
        ·
          refine ⟨41859310530603193925669435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27906207020402129283779623 41859310530603193925669435)
          ·
            refine ⟨62788965795904790888504153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41859310530603193925669435 62788965795904790888504153)
            ·
              refine ⟨47091724346928593166378115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62788965795904790888504153 47091724346928593166378115)
              ·
                refine ⟨70637586520392889749567173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47091724346928593166378115 70637586520392889749567173)
                ·
                  refine ⟨13244547472573666828043845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70637586520392889749567173 13244547472573666828043845)
                  ·
                    refine ⟨2483352651107562530258221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13244547472573666828043845 2483352651107562530258221)
                    ·
                      refine ⟨931257244165335948846833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483352651107562530258221 931257244165335948846833)
                      ·
                        rfl

theorem cell23_1813617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_1813617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813617 prefixEnd_1813617 := by exact prefixLift 1813617
  have htrace : WordTrace (prefixWord ++ tailWord_1813617) baseStart_1813617 baseEnd_1813617 := by
    simpa [prefixWord, tailWord_1813617, baseEnd_1813617] using wordTrace_append hprefix tailTrace_1813617
  have hstable : (prefixWord ++ tailWord_1813617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813617).length < 2 ^ (prefixWord ++ tailWord_1813617).sum := by decide
  have hdescent : baseEnd_1813617 < baseStart_1813617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813664 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1813664 : Nat := 118140960795 + 1813664 * 2 ^ 59
def prefixEnd_1813664 : Nat := 4983230072969 + 3 ^ 40 * 1813664 * 2
def baseEnd_1813664 : Nat := 931281377756097264959117

theorem tailTrace_1813664 : CollatzResearch.WordTrace tailWord_1813664 prefixEnd_1813664 931281377756097264959117 := by
  unfold tailWord_1813664
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074880250706275997960023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44099840334275034663946697 33074880250706275997960023)
  ·
    refine ⟨49612320376059413996940035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33074880250706275997960023 49612320376059413996940035)
    ·
      refine ⟨74418480564089120995410053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49612320376059413996940035 74418480564089120995410053)
      ·
        refine ⟨13953465105766710186639385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74418480564089120995410053 13953465105766710186639385)
        ·
          refine ⟨10465098829325032639979539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13953465105766710186639385 10465098829325032639979539)
          ·
            refine ⟨15697648243987548959969309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465098829325032639979539 15697648243987548959969309)
            ·
              refine ⟨5886618091495330859988491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15697648243987548959969309 5886618091495330859988491)
              ·
                refine ⟨8829927137242996289982737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886618091495330859988491 8829927137242996289982737)
                ·
                  refine ⟨6622445352932247217487053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8829927137242996289982737 6622445352932247217487053)
                  ·
                    refine ⟨2483417007349592706557645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6622445352932247217487053 2483417007349592706557645)
                    ·
                      refine ⟨931281377756097264959117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483417007349592706557645 931281377756097264959117)
                      ·
                        rfl

theorem cell23_1813664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1813664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813664 prefixEnd_1813664 := by exact prefixLift 1813664
  have htrace : WordTrace (prefixWord ++ tailWord_1813664) baseStart_1813664 baseEnd_1813664 := by
    simpa [prefixWord, tailWord_1813664, baseEnd_1813664] using wordTrace_append hprefix tailTrace_1813664
  have hstable : (prefixWord ++ tailWord_1813664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813664).length < 2 ^ (prefixWord ++ tailWord_1813664).sum := by decide
  have hdescent : baseEnd_1813664 < baseStart_1813664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813667 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 4, 5]
def baseStart_1813667 : Nat := 118140960795 + 1813667 * 2 ^ 59
def prefixEnd_1813667 : Nat := 4983230072969 + 3 ^ 40 * 1813667 * 2
def baseEnd_1813667 : Nat := 310427639399353584407201

theorem tailTrace_1813667 : CollatzResearch.WordTrace tailWord_1813667 prefixEnd_1813667 310427639399353584407201 := by
  unfold tailWord_1813667
  simp only [CollatzResearch.WordTrace]
  refine ⟨66149869920401683508279255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44099913280267789005519503 66149869920401683508279255)
  ·
    refine ⟨99224804880602525262418883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66149869920401683508279255 99224804880602525262418883)
    ·
      refine ⟨148837207320903787893628325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99224804880602525262418883 148837207320903787893628325)
      ·
        refine ⟨27906976372669460230055311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148837207320903787893628325 27906976372669460230055311)
        ·
          refine ⟨41860464559004190345082967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27906976372669460230055311 41860464559004190345082967)
          ·
            refine ⟨62790696838506285517624451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41860464559004190345082967 62790696838506285517624451)
            ·
              refine ⟨94186045257759428276436677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62790696838506285517624451 94186045257759428276436677)
              ·
                refine ⟨17659883485829892801831877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94186045257759428276436677 17659883485829892801831877)
                ·
                  refine ⟨3311228153593104900343477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17659883485829892801831877 3311228153593104900343477)
                  ·
                    refine ⟨310427639399353584407201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3311228153593104900343477 310427639399353584407201)
                    ·
                      rfl

theorem cell23_1813667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 5].length) (baseStart_1813667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813667 prefixEnd_1813667 := by exact prefixLift 1813667
  have htrace : WordTrace (prefixWord ++ tailWord_1813667) baseStart_1813667 baseEnd_1813667 := by
    simpa [prefixWord, tailWord_1813667, baseEnd_1813667] using wordTrace_append hprefix tailTrace_1813667
  have hstable : (prefixWord ++ tailWord_1813667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813667).length < 2 ^ (prefixWord ++ tailWord_1813667).sum := by decide
  have hdescent : baseEnd_1813667 < baseStart_1813667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813686 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1813686 : Nat := 118140960795 + 1813686 * 2 ^ 59
def prefixEnd_1813686 : Nat := 4983230072969 + 3 ^ 40 * 1813686 * 2
def baseEnd_1813686 : Nat := 931292674330496178884017

theorem tailTrace_1813686 : CollatzResearch.WordTrace tailWord_1813686 prefixEnd_1813686 931292674330496178884017 := by
  unfold tailWord_1813686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134410181708303109576307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44100375271555233168813941 4134410181708303109576307)
  ·
    refine ⟨6201615272562454664364461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4134410181708303109576307 6201615272562454664364461)
    ·
      refine ⟨2325605727210920499136673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6201615272562454664364461 2325605727210920499136673)
      ·
        refine ⟨1744204295408190374352505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2325605727210920499136673 1744204295408190374352505)
        ·
          refine ⟨1308153221556142780764379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744204295408190374352505 1308153221556142780764379)
          ·
            refine ⟨1962229832334214171146569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308153221556142780764379 1962229832334214171146569)
            ·
              refine ⟨1471672374250660628359927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962229832334214171146569 1471672374250660628359927)
              ·
                refine ⟨2207508561375990942539891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471672374250660628359927 2207508561375990942539891)
                ·
                  refine ⟨3311262842063986413809837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207508561375990942539891 3311262842063986413809837)
                  ·
                    refine ⟨1241723565773994905178689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311262842063986413809837 1241723565773994905178689)
                    ·
                      refine ⟨931292674330496178884017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241723565773994905178689 931292674330496178884017)
                      ·
                        rfl

theorem cell23_1813686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1813686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813686 prefixEnd_1813686 := by exact prefixLift 1813686
  have htrace : WordTrace (prefixWord ++ tailWord_1813686) baseStart_1813686 baseEnd_1813686 := by
    simpa [prefixWord, tailWord_1813686, baseEnd_1813686] using wordTrace_append hprefix tailTrace_1813686
  have hstable : (prefixWord ++ tailWord_1813686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813686).length < 2 ^ (prefixWord ++ tailWord_1813686).sum := by decide
  have hdescent : baseEnd_1813686 < baseStart_1813686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813704 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1813704 : Nat := 118140960795 + 1813704 * 2 ^ 59
def prefixEnd_1813704 : Nat := 4983230072969 + 3 ^ 40 * 1813704 * 2
def baseEnd_1813704 : Nat := 931301916982277108458933

theorem tailTrace_1813704 : CollatzResearch.WordTrace tailWord_1813704 prefixEnd_1813704 931301916982277108458933 := by
  unfold tailWord_1813704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33075609710633819413688083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44100812947511759218250777 33075609710633819413688083)
  ·
    refine ⟨49613414565950729120532125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33075609710633819413688083 49613414565950729120532125)
    ·
      refine ⟨18605030462231523420199547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49613414565950729120532125 18605030462231523420199547)
      ·
        refine ⟨27907545693347285130299321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18605030462231523420199547 27907545693347285130299321)
        ·
          refine ⟨20930659270010463847724491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27907545693347285130299321 20930659270010463847724491)
          ·
            refine ⟨31395988905015695771586737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20930659270010463847724491 31395988905015695771586737)
            ·
              refine ⟨23546991678761771828690053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31395988905015695771586737 23546991678761771828690053)
              ·
                refine ⟨4415060939767832217879385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23546991678761771828690053 4415060939767832217879385)
                ·
                  refine ⟨3311295704825874163409539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415060939767832217879385 3311295704825874163409539)
                  ·
                    refine ⟨4966943557238811245114309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311295704825874163409539 4966943557238811245114309)
                    ·
                      refine ⟨931301916982277108458933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4966943557238811245114309 931301916982277108458933)
                      ·
                        rfl

theorem cell23_1813704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1813704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813704 prefixEnd_1813704 := by exact prefixLift 1813704
  have htrace : WordTrace (prefixWord ++ tailWord_1813704) baseStart_1813704 baseEnd_1813704 := by
    simpa [prefixWord, tailWord_1813704, baseEnd_1813704] using wordTrace_append hprefix tailTrace_1813704
  have hstable : (prefixWord ++ tailWord_1813704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813704).length < 2 ^ (prefixWord ++ tailWord_1813704).sum := by decide
  have hdescent : baseEnd_1813704 < baseStart_1813704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813741 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1813741 : Nat := 118140960795 + 1813741 * 2 ^ 59
def prefixEnd_1813741 : Nat := 4983230072969 + 3 ^ 40 * 1813741 * 2
def baseEnd_1813741 : Nat := 931320915766493463696263

theorem tailTrace_1813741 : CollatzResearch.WordTrace tailWord_1813741 prefixEnd_1813741 931320915766493463696263 := by
  unfold tailWord_1813741
  simp only [CollatzResearch.WordTrace]
  refine ⟨66152568922133594146473077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44101712614755729430982051 66152568922133594146473077)
  ·
    refine ⟨6201803336450024451231851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66152568922133594146473077 6201803336450024451231851)
    ·
      refine ⟨9302705004675036676847777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201803336450024451231851 9302705004675036676847777)
      ·
        refine ⟨6977028753506277507635833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9302705004675036676847777 6977028753506277507635833)
        ·
          refine ⟨5232771565129708130726875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6977028753506277507635833 5232771565129708130726875)
          ·
            refine ⟨7849157347694562196090313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232771565129708130726875 7849157347694562196090313)
            ·
              refine ⟨5886868010770921647067735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7849157347694562196090313 5886868010770921647067735)
              ·
                refine ⟨8830302016156382470601603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886868010770921647067735 8830302016156382470601603)
                ·
                  refine ⟨13245453024234573705902405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8830302016156382470601603 13245453024234573705902405)
                  ·
                    refine ⟨2483522442043982569856701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13245453024234573705902405 2483522442043982569856701)
                    ·
                      refine ⟨931320915766493463696263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483522442043982569856701 931320915766493463696263)
                      ·
                        rfl

theorem cell23_1813741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1813741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813741 prefixEnd_1813741 := by exact prefixLift 1813741
  have htrace : WordTrace (prefixWord ++ tailWord_1813741) baseStart_1813741 baseEnd_1813741 := by
    simpa [prefixWord, tailWord_1813741, baseEnd_1813741] using wordTrace_append hprefix tailTrace_1813741
  have hstable : (prefixWord ++ tailWord_1813741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813741).length < 2 ^ (prefixWord ++ tailWord_1813741).sum := by decide
  have hdescent : baseEnd_1813741 < baseStart_1813741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813758 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1813758 : Nat := 118140960795 + 1813758 * 2 ^ 59
def prefixEnd_1813758 : Nat := 4983230072969 + 3 ^ 40 * 1813758 * 2
def baseEnd_1813758 : Nat := 931329644937619897183685

theorem tailTrace_1813758 : CollatzResearch.WordTrace tailWord_1813758 prefixEnd_1813758 931329644937619897183685 := by
  unfold tailWord_1813758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269148620384000756230241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44102125975381337366561285 8269148620384000756230241)
  ·
    refine ⟨6201861465288000567172681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8269148620384000756230241 6201861465288000567172681)
    ·
      refine ⟨4651396098966000425379511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6201861465288000567172681 4651396098966000425379511)
      ·
        refine ⟨6977094148449000638069267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651396098966000425379511 6977094148449000638069267)
        ·
          refine ⟨10465641222673500957103901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977094148449000638069267 10465641222673500957103901)
          ·
            refine ⟨3924615458502562858913963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10465641222673500957103901 3924615458502562858913963)
            ·
              refine ⟨5886923187753844288370945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924615458502562858913963 5886923187753844288370945)
              ·
                refine ⟨4415192390815383216278209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886923187753844288370945 4415192390815383216278209)
                ·
                  refine ⟨3311394293111537412208657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415192390815383216278209 3311394293111537412208657)
                  ·
                    refine ⟨2483545719833653059156493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3311394293111537412208657 2483545719833653059156493)
                    ·
                      refine ⟨931329644937619897183685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483545719833653059156493 931329644937619897183685)
                      ·
                        rfl

theorem cell23_1813758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1813758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813758 prefixEnd_1813758 := by exact prefixLift 1813758
  have htrace : WordTrace (prefixWord ++ tailWord_1813758) baseStart_1813758 baseEnd_1813758 := by
    simpa [prefixWord, tailWord_1813758, baseEnd_1813758] using wordTrace_append hprefix tailTrace_1813758
  have hstable : (prefixWord ++ tailWord_1813758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813758).length < 2 ^ (prefixWord ++ tailWord_1813758).sum := by decide
  have hdescent : baseEnd_1813758 < baseStart_1813758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813781 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_1813781 : Nat := 118140960795 + 1813781 * 2 ^ 59
def prefixEnd_1813781 : Nat := 4983230072969 + 3 ^ 40 * 1813781 * 2
def baseEnd_1813781 : Nat := 931341454992673307196079

theorem tailTrace_1813781 : CollatzResearch.WordTrace tailWord_1813781 prefixEnd_1813781 931341454992673307196079 := by
  unfold tailWord_1813781
  simp only [CollatzResearch.WordTrace]
  refine ⟨66154027841988680977929197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44102685227992453985286131 66154027841988680977929197)
  ·
    refine ⟨24807760440745755366723449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66154027841988680977929197 24807760440745755366723449)
    ·
      refine ⟨18605820330559316525042587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24807760440745755366723449 18605820330559316525042587)
      ·
        refine ⟨27908730495838974787563881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18605820330559316525042587 27908730495838974787563881)
        ·
          refine ⟨20931547871879231090672911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27908730495838974787563881 20931547871879231090672911)
          ·
            refine ⟨31397321807818846636009367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20931547871879231090672911 31397321807818846636009367)
            ·
              refine ⟨47095982711728269954014051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31397321807818846636009367 47095982711728269954014051)
              ·
                refine ⟨70643974067592404931021077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47095982711728269954014051 70643974067592404931021077)
                ·
                  refine ⟨3311436284418393981141613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70643974067592404931021077 3311436284418393981141613)
                  ·
                    refine ⟨1241788606656897742928105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311436284418393981141613 1241788606656897742928105)
                    ·
                      refine ⟨931341454992673307196079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241788606656897742928105 931341454992673307196079)
                      ·
                        rfl

theorem cell23_1813781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_1813781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813781 prefixEnd_1813781 := by exact prefixLift 1813781
  have htrace : WordTrace (prefixWord ++ tailWord_1813781) baseStart_1813781 baseEnd_1813781 := by
    simpa [prefixWord, tailWord_1813781, baseEnd_1813781] using wordTrace_append hprefix tailTrace_1813781
  have hstable : (prefixWord ++ tailWord_1813781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813781).length < 2 ^ (prefixWord ++ tailWord_1813781).sum := by decide
  have hdescent : baseEnd_1813781 < baseStart_1813781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813791 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 3, 5]
def baseStart_1813791 : Nat := 118140960795 + 1813791 * 2 ^ 59
def prefixEnd_1813791 : Nat := 4983230072969 + 3 ^ 40 * 1813791 * 2
def baseEnd_1813791 : Nat := 310448863266406089357011

theorem tailTrace_1813791 : CollatzResearch.WordTrace tailWord_1813791 prefixEnd_1813791 310448863266406089357011 := by
  unfold tailWord_1813791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66154392571952452685793227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44102928381301635123862151 66154392571952452685793227)
  ·
    refine ⟨99231588857928679028689841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66154392571952452685793227 99231588857928679028689841)
    ·
      refine ⟨74423691643446509271517381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99231588857928679028689841 74423691643446509271517381)
      ·
        refine ⟨13954442183146220488409509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74423691643446509271517381 13954442183146220488409509)
        ·
          refine ⟨2616457909339916341576783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13954442183146220488409509 2616457909339916341576783)
          ·
            refine ⟨3924686864009874512365175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616457909339916341576783 3924686864009874512365175)
            ·
              refine ⟨5887030296014811768547763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924686864009874512365175 5887030296014811768547763)
              ·
                refine ⟨8830545444022217652821645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887030296014811768547763 8830545444022217652821645)
                ·
                  refine ⟨3311454541508331619808117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830545444022217652821645 3311454541508331619808117)
                  ·
                    refine ⟨310448863266406089357011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3311454541508331619808117 310448863266406089357011)
                    ·
                      rfl

theorem cell23_1813791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_1813791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813791 prefixEnd_1813791 := by exact prefixLift 1813791
  have htrace : WordTrace (prefixWord ++ tailWord_1813791) baseStart_1813791 baseEnd_1813791 := by
    simpa [prefixWord, tailWord_1813791, baseEnd_1813791] using wordTrace_append hprefix tailTrace_1813791
  have hstable : (prefixWord ++ tailWord_1813791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813791).length < 2 ^ (prefixWord ++ tailWord_1813791).sum := by decide
  have hdescent : baseEnd_1813791 < baseStart_1813791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813824 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1813824 : Nat := 118140960795 + 1813824 * 2 ^ 59
def prefixEnd_1813824 : Nat := 4983230072969 + 3 ^ 40 * 1813824 * 2
def baseEnd_1813824 : Nat := 931363534660816638958381

theorem tailTrace_1813824 : CollatzResearch.WordTrace tailWord_1813824 prefixEnd_1813824 931363534660816638958381 := by
  unfold tailWord_1813824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077798090416449660872263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44103730787221932881163017 33077798090416449660872263)
  ·
    refine ⟨49616697135624674491308395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33077798090416449660872263 49616697135624674491308395)
    ·
      refine ⟨74425045703437011736962593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49616697135624674491308395 74425045703437011736962593)
      ·
        refine ⟨55818784277577758802721945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74425045703437011736962593 55818784277577758802721945)
        ·
          refine ⟨41864088208183319102041459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55818784277577758802721945 41864088208183319102041459)
          ·
            refine ⟨62796132312274978653062189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41864088208183319102041459 62796132312274978653062189)
            ·
              refine ⟨23548549617103116994898321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62796132312274978653062189 23548549617103116994898321)
              ·
                refine ⟨17661412212827337746173741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23548549617103116994898321 17661412212827337746173741)
                ·
                  refine ⟨6623029579810251654815153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17661412212827337746173741 6623029579810251654815153)
                  ·
                    refine ⟨4967272184857688741111365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6623029579810251654815153 4967272184857688741111365)
                    ·
                      refine ⟨931363534660816638958381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4967272184857688741111365 931363534660816638958381)
                      ·
                        rfl

theorem cell23_1813824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1813824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813824 prefixEnd_1813824 := by exact prefixLift 1813824
  have htrace : WordTrace (prefixWord ++ tailWord_1813824) baseStart_1813824 baseEnd_1813824 := by
    simpa [prefixWord, tailWord_1813824, baseEnd_1813824] using wordTrace_append hprefix tailTrace_1813824
  have hstable : (prefixWord ++ tailWord_1813824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813824).length < 2 ^ (prefixWord ++ tailWord_1813824).sum := by decide
  have hdescent : baseEnd_1813824 < baseStart_1813824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813828 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1813828 : Nat := 118140960795 + 1813828 * 2 ^ 59
def prefixEnd_1813828 : Nat := 4983230072969 + 3 ^ 40 * 1813828 * 2
def baseEnd_1813828 : Nat := 931365588583434623308363

theorem tailTrace_1813828 : CollatzResearch.WordTrace tailWord_1813828 prefixEnd_1813828 931365588583434623308363 := by
  unfold tailWord_1813828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077871036409204002445069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44103828048545605336593425 33077871036409204002445069)
  ·
    refine ⟨12404201638653451500916901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33077871036409204002445069 12404201638653451500916901)
    ·
      refine ⟨2325787807247522156421919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12404201638653451500916901 2325787807247522156421919)
      ·
        refine ⟨3488681710871283234632879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325787807247522156421919 3488681710871283234632879)
        ·
          refine ⟨5233022566306924851949319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488681710871283234632879 5233022566306924851949319)
          ·
            refine ⟨7849533849460387277923979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233022566306924851949319 7849533849460387277923979)
            ·
              refine ⟨11774300774190580916885969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849533849460387277923979 11774300774190580916885969)
              ·
                refine ⟨8830725580642935687664477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774300774190580916885969 8830725580642935687664477)
                ·
                  refine ⟨3311522092741100882874179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830725580642935687664477 3311522092741100882874179)
                  ·
                    refine ⟨4967283139111651324311269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311522092741100882874179 4967283139111651324311269)
                    ·
                      refine ⟨931365588583434623308363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4967283139111651324311269 931365588583434623308363)
                      ·
                        rfl

theorem cell23_1813828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1813828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813828 prefixEnd_1813828 := by exact prefixLift 1813828
  have htrace : WordTrace (prefixWord ++ tailWord_1813828) baseStart_1813828 baseEnd_1813828 := by
    simpa [prefixWord, tailWord_1813828, baseEnd_1813828] using wordTrace_append hprefix tailTrace_1813828
  have hstable : (prefixWord ++ tailWord_1813828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813828).length < 2 ^ (prefixWord ++ tailWord_1813828).sum := by decide
  have hdescent : baseEnd_1813828 < baseStart_1813828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813831 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1813831 : Nat := 118140960795 + 1813831 * 2 ^ 59
def prefixEnd_1813831 : Nat := 4983230072969 + 3 ^ 40 * 1813831 * 2
def baseEnd_1813831 : Nat := 931367129025398111570849

theorem tailTrace_1813831 : CollatzResearch.WordTrace tailWord_1813831 prefixEnd_1813831 931367129025398111570849 := by
  unfold tailWord_1813831
  simp only [CollatzResearch.WordTrace]
  refine ⟨66155851491807539517249347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44103900994538359678166231 66155851491807539517249347)
  ·
    refine ⟨99233777237711309275874021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66155851491807539517249347 99233777237711309275874021)
    ·
      refine ⟨18606333232070870489226379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99233777237711309275874021 18606333232070870489226379)
      ·
        refine ⟨27909499848106305733839569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18606333232070870489226379 27909499848106305733839569)
        ·
          refine ⟨20932124886079729300379677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27909499848106305733839569 20932124886079729300379677)
          ·
            refine ⟨7849546832279898487642379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20932124886079729300379677 7849546832279898487642379)
            ·
              refine ⟨11774320248419847731463569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849546832279898487642379 11774320248419847731463569)
              ·
                refine ⟨8830740186314885798597677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774320248419847731463569 8830740186314885798597677)
                ·
                  refine ⟨3311527569868082174474129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830740186314885798597677 3311527569868082174474129)
                  ·
                    refine ⟨2483645677401061630855597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3311527569868082174474129 2483645677401061630855597)
                    ·
                      refine ⟨931367129025398111570849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483645677401061630855597 931367129025398111570849)
                      ·
                        rfl

theorem cell23_1813831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1813831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813831 prefixEnd_1813831 := by exact prefixLift 1813831
  have htrace : WordTrace (prefixWord ++ tailWord_1813831) baseStart_1813831 baseEnd_1813831 := by
    simpa [prefixWord, tailWord_1813831, baseEnd_1813831] using wordTrace_append hprefix tailTrace_1813831
  have hstable : (prefixWord ++ tailWord_1813831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813831).length < 2 ^ (prefixWord ++ tailWord_1813831).sum := by decide
  have hdescent : baseEnd_1813831 < baseStart_1813831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813841 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_1813841 : Nat := 118140960795 + 1813841 * 2 ^ 59
def prefixEnd_1813841 : Nat := 4983230072969 + 3 ^ 40 * 1813841 * 2
def baseEnd_1813841 : Nat := 931372263831943072445803

theorem tailTrace_1813841 : CollatzResearch.WordTrace tailWord_1813841 prefixEnd_1813841 931372263831943072445803 := by
  unfold tailWord_1813841
  simp only [CollatzResearch.WordTrace]
  refine ⟨66156216221771311225113377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44104144147847540816742251 66156216221771311225113377)
  ·
    refine ⟨49617162166328483418835033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66156216221771311225113377 49617162166328483418835033)
    ·
      refine ⟨37212871624746362564126275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49617162166328483418835033 37212871624746362564126275)
      ·
        refine ⟨55819307437119543846189413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37212871624746362564126275 55819307437119543846189413)
        ·
          refine ⟨10466120144459914471160515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55819307437119543846189413 10466120144459914471160515)
          ·
            refine ⟨15699180216689871706740773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10466120144459914471160515 15699180216689871706740773)
            ·
              refine ⟨2943596290629350945013895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15699180216689871706740773 2943596290629350945013895)
              ·
                refine ⟨4415394435944026417520843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943596290629350945013895 4415394435944026417520843)
                ·
                  refine ⟨6623091653916039626281265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415394435944026417520843 6623091653916039626281265)
                  ·
                    refine ⟨4967318740437029719710949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6623091653916039626281265 4967318740437029719710949)
                    ·
                      refine ⟨931372263831943072445803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4967318740437029719710949 931372263831943072445803)
                      ·
                        rfl

theorem cell23_1813841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_1813841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813841 prefixEnd_1813841 := by exact prefixLift 1813841
  have htrace : WordTrace (prefixWord ++ tailWord_1813841) baseStart_1813841 baseEnd_1813841 := by
    simpa [prefixWord, tailWord_1813841, baseEnd_1813841] using wordTrace_append hprefix tailTrace_1813841
  have hstable : (prefixWord ++ tailWord_1813841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813841).length < 2 ^ (prefixWord ++ tailWord_1813841).sum := by decide
  have hdescent : baseEnd_1813841 < baseStart_1813841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813845 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1813845 : Nat := 118140960795 + 1813845 * 2 ^ 59
def prefixEnd_1813845 : Nat := 4983230072969 + 3 ^ 40 * 1813845 * 2
def baseEnd_1813845 : Nat := 931374317754561056795785

theorem tailTrace_1813845 : CollatzResearch.WordTrace tailWord_1813845 prefixEnd_1813845 931374317754561056795785 := by
  unfold tailWord_1813845
  simp only [CollatzResearch.WordTrace]
  refine ⟨66156362113756819908258989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44104241409171213272172659 66156362113756819908258989)
  ·
    refine ⟨24808635792658807465597121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66156362113756819908258989 24808635792658807465597121)
    ·
      refine ⟨18606476844494105599197841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24808635792658807465597121 18606476844494105599197841)
      ·
        refine ⟨13954857633370579199398381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606476844494105599197841 13954857633370579199398381)
        ·
          refine ⟨5233071612513967199774393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13954857633370579199398381 5233071612513967199774393)
          ·
            refine ⟨3924803709385475399830795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233071612513967199774393 3924803709385475399830795)
            ·
              refine ⟨5887205564078213099746193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924803709385475399830795 5887205564078213099746193)
              ·
                refine ⟨4415404173058659824809645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887205564078213099746193 4415404173058659824809645)
                ·
                  refine ⟨1655776564896997434303617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4415404173058659824809645 1655776564896997434303617)
                  ·
                    refine ⟨1241832423672748075727713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655776564896997434303617 1241832423672748075727713)
                    ·
                      refine ⟨931374317754561056795785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241832423672748075727713 931374317754561056795785)
                      ·
                        rfl

theorem cell23_1813845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1813845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813845 prefixEnd_1813845 := by exact prefixLift 1813845
  have htrace : WordTrace (prefixWord ++ tailWord_1813845) baseStart_1813845 baseEnd_1813845 := by
    simpa [prefixWord, tailWord_1813845, baseEnd_1813845] using wordTrace_append hprefix tailTrace_1813845
  have hstable : (prefixWord ++ tailWord_1813845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813845).length < 2 ^ (prefixWord ++ tailWord_1813845).sum := by decide
  have hdescent : baseEnd_1813845 < baseStart_1813845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813861 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1813861 : Nat := 118140960795 + 1813861 * 2 ^ 59
def prefixEnd_1813861 : Nat := 4983230072969 + 3 ^ 40 * 1813861 * 2
def baseEnd_1813861 : Nat := 931382533445032994195711

theorem tailTrace_1813861 : CollatzResearch.WordTrace tailWord_1813861 prefixEnd_1813861 931382533445032994195711 := by
  unfold tailWord_1813861
  simp only [CollatzResearch.WordTrace]
  refine ⟨66156945681698854640841437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44104630454465903093894291 66156945681698854640841437)
  ·
    refine ⟨24808854630637070490315539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66156945681698854640841437 24808854630637070490315539)
    ·
      refine ⟨37213281945955605735473309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24808854630637070490315539 37213281945955605735473309)
      ·
        refine ⟨13954980729733352150802491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37213281945955605735473309 13954980729733352150802491)
        ·
          refine ⟨20932471094600028226203737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954980729733352150802491 20932471094600028226203737)
          ·
            refine ⟨15699353320950021169652803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20932471094600028226203737 15699353320950021169652803)
            ·
              refine ⟨23549029981425031754479205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15699353320950021169652803 23549029981425031754479205)
              ·
                refine ⟨4415443121517193453964851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23549029981425031754479205 4415443121517193453964851)
                ·
                  refine ⟨6623164682275790180947277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415443121517193453964851 6623164682275790180947277)
                  ·
                    refine ⟨2483686755853421317855229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6623164682275790180947277 2483686755853421317855229)
                    ·
                      refine ⟨931382533445032994195711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483686755853421317855229 931382533445032994195711)
                      ·
                        rfl

theorem cell23_1813861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1813861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813861 prefixEnd_1813861 := by exact prefixLift 1813861
  have htrace : WordTrace (prefixWord ++ tailWord_1813861) baseStart_1813861 baseEnd_1813861 := by
    simpa [prefixWord, tailWord_1813861, baseEnd_1813861] using wordTrace_append hprefix tailTrace_1813861
  have hstable : (prefixWord ++ tailWord_1813861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813861).length < 2 ^ (prefixWord ++ tailWord_1813861).sum := by decide
  have hdescent : baseEnd_1813861 < baseStart_1813861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813951 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1813951 : Nat := 118140960795 + 1813951 * 2 ^ 59
def prefixEnd_1813951 : Nat := 4983230072969 + 3 ^ 40 * 1813951 * 2
def baseEnd_1813951 : Nat := 931428746703937642070297

theorem tailTrace_1813951 : CollatzResearch.WordTrace tailWord_1813951 prefixEnd_1813951 931428746703937642070297 := by
  unfold tailWord_1813951
  simp only [CollatzResearch.WordTrace]
  refine ⟨66160228251372800011617707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44106818834248533341078471 66160228251372800011617707)
  ·
    refine ⟨99240342377059200017426561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66160228251372800011617707 99240342377059200017426561)
    ·
      refine ⟨74430256782794400013069921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99240342377059200017426561 74430256782794400013069921)
      ·
        refine ⟨55822692587095800009802441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74430256782794400013069921 55822692587095800009802441)
        ·
          refine ⟨41867019440321850007351831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55822692587095800009802441 41867019440321850007351831)
          ·
            refine ⟨62800529160482775011027747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41867019440321850007351831 62800529160482775011027747)
            ·
              refine ⟨94200793740724162516541621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62800529160482775011027747 94200793740724162516541621)
              ·
                refine ⟨8831324413192890235925777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94200793740724162516541621 8831324413192890235925777)
                ·
                  refine ⟨6623493309894667676944333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831324413192890235925777 6623493309894667676944333)
                  ·
                    refine ⟨2483809991210500378854125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6623493309894667676944333 2483809991210500378854125)
                    ·
                      refine ⟨931428746703937642070297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483809991210500378854125 931428746703937642070297)
                      ·
                        rfl

theorem cell23_1813951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1813951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813951 prefixEnd_1813951 := by exact prefixLift 1813951
  have htrace : WordTrace (prefixWord ++ tailWord_1813951) baseStart_1813951 baseEnd_1813951 := by
    simpa [prefixWord, tailWord_1813951, baseEnd_1813951] using wordTrace_append hprefix tailTrace_1813951
  have hstable : (prefixWord ++ tailWord_1813951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813951).length < 2 ^ (prefixWord ++ tailWord_1813951).sum := by decide
  have hdescent : baseEnd_1813951 < baseStart_1813951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1813952 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2]
def baseStart_1813952 : Nat := 118140960795 + 1813952 * 2 ^ 59
def prefixEnd_1813952 : Nat := 4983230072969 + 3 ^ 40 * 1813952 * 2
def baseEnd_1813952 : Nat := 931429260184592138157793

theorem tailTrace_1813952 : CollatzResearch.WordTrace tailWord_1813952 prefixEnd_1813952 931429260184592138157793 := by
  unfold tailWord_1813952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080132362184588591202055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44106843149579451454936073 33080132362184588591202055)
  ·
    refine ⟨49620198543276882886803083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33080132362184588591202055 49620198543276882886803083)
    ·
      refine ⟨74430297814915324330204625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49620198543276882886803083 74430297814915324330204625)
      ·
        refine ⟨55822723361186493247653469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74430297814915324330204625 55822723361186493247653469)
        ·
          refine ⟨20933521260444934967870051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55822723361186493247653469 20933521260444934967870051)
          ·
            refine ⟨31400281890667402451805077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20933521260444934967870051 31400281890667402451805077)
            ·
              refine ⟨1471888213625034489928363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31400281890667402451805077 1471888213625034489928363)
              ·
                refine ⟨2207832320437551734892545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471888213625034489928363 2207832320437551734892545)
                ·
                  refine ⟨1655874240328163801169409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207832320437551734892545 1655874240328163801169409)
                  ·
                    refine ⟨1241905680246122850877057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1655874240328163801169409 1241905680246122850877057)
                    ·
                      refine ⟨931429260184592138157793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241905680246122850877057 931429260184592138157793)
                      ·
                        rfl

theorem cell23_1813952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_1813952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1813952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1813952 prefixEnd_1813952 := by exact prefixLift 1813952
  have htrace : WordTrace (prefixWord ++ tailWord_1813952) baseStart_1813952 baseEnd_1813952 := by
    simpa [prefixWord, tailWord_1813952, baseEnd_1813952] using wordTrace_append hprefix tailTrace_1813952
  have hstable : (prefixWord ++ tailWord_1813952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1813952).length < 2 ^ (prefixWord ++ tailWord_1813952).sum := by decide
  have hdescent : baseEnd_1813952 < baseStart_1813952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1813952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814008 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_1814008 : Nat := 118140960795 + 1814008 * 2 ^ 59
def prefixEnd_1814008 : Nat := 4983230072969 + 3 ^ 40 * 1814008 * 2
def baseEnd_1814008 : Nat := 931458015101243919057535

theorem tailTrace_1814008 : CollatzResearch.WordTrace tailWord_1814008 prefixEnd_1814008 931458015101243919057535 := by
  unfold tailWord_1814008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33081153606083149373221339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44108204808110865830961785 33081153606083149373221339)
  ·
    refine ⟨49621730409124724059832009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33081153606083149373221339 49621730409124724059832009)
    ·
      refine ⟨37216297806843543044874007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49621730409124724059832009 37216297806843543044874007)
      ·
        refine ⟨55824446710265314567311011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37216297806843543044874007 55824446710265314567311011)
        ·
          refine ⟨83736670065397971850966517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55824446710265314567311011 83736670065397971850966517)
          ·
            refine ⟨7850312818631059861028111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83736670065397971850966517 7850312818631059861028111)
            ·
              refine ⟨11775469227946589791542167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850312818631059861028111 11775469227946589791542167)
              ·
                refine ⟨17663203841919884687313251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775469227946589791542167 17663203841919884687313251)
                ·
                  refine ⟨26494805762879827030969877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17663203841919884687313251 26494805762879827030969877)
                  ·
                    refine ⟨1241944020134991892076713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26494805762879827030969877 1241944020134991892076713)
                    ·
                      refine ⟨931458015101243919057535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241944020134991892076713 931458015101243919057535)
                      ·
                        rfl

theorem cell23_1814008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_1814008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814008 prefixEnd_1814008 := by exact prefixLift 1814008
  have htrace : WordTrace (prefixWord ++ tailWord_1814008) baseStart_1814008 baseEnd_1814008 := by
    simpa [prefixWord, tailWord_1814008, baseEnd_1814008] using wordTrace_append hprefix tailTrace_1814008
  have hstable : (prefixWord ++ tailWord_1814008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814008).length < 2 ^ (prefixWord ++ tailWord_1814008).sum := by decide
  have hdescent : baseEnd_1814008 < baseStart_1814008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814011 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3]
def baseStart_1814011 : Nat := 118140960795 + 1814011 * 2 ^ 59
def prefixEnd_1814011 : Nat := 4983230072969 + 3 ^ 40 * 1814011 * 2
def baseEnd_1814011 : Nat := 931459555543207407320021

theorem tailTrace_1814011 : CollatzResearch.WordTrace tailWord_1814011 prefixEnd_1814011 931459555543207407320021 := by
  unfold tailWord_1814011
  simp only [CollatzResearch.WordTrace]
  refine ⟨66162416631155430258801887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44108277754103620172534591 66162416631155430258801887)
  ·
    refine ⟨99243624946733145388202831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66162416631155430258801887 99243624946733145388202831)
    ·
      refine ⟨148865437420099718082304247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99243624946733145388202831 148865437420099718082304247)
      ·
        refine ⟨223298156130149577123456371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148865437420099718082304247 223298156130149577123456371)
        ·
          refine ⟨334947234195224365685184557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223298156130149577123456371 334947234195224365685184557)
          ·
            refine ⟨125605212823209137131944209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334947234195224365685184557 125605212823209137131944209)
            ·
              refine ⟨94203909617406852848958157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125605212823209137131944209 94203909617406852848958157)
              ·
                refine ⟨35326466106527569818359309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94203909617406852848958157 35326466106527569818359309)
                ·
                  refine ⟨13247424789947838681884741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35326466106527569818359309 13247424789947838681884741)
                  ·
                    refine ⟨2483892148115219752853389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13247424789947838681884741 2483892148115219752853389)
                    ·
                      refine ⟨931459555543207407320021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2483892148115219752853389 931459555543207407320021)
                      ·
                        rfl

theorem cell23_1814011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 3].length) (baseStart_1814011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814011 prefixEnd_1814011 := by exact prefixLift 1814011
  have htrace : WordTrace (prefixWord ++ tailWord_1814011) baseStart_1814011 baseEnd_1814011 := by
    simpa [prefixWord, tailWord_1814011, baseEnd_1814011] using wordTrace_append hprefix tailTrace_1814011
  have hstable : (prefixWord ++ tailWord_1814011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814011).length < 2 ^ (prefixWord ++ tailWord_1814011).sum := by decide
  have hdescent : baseEnd_1814011 < baseStart_1814011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814035 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 1, 4]
def baseStart_1814035 : Nat := 118140960795 + 1814035 * 2 ^ 59
def prefixEnd_1814035 : Nat := 4983230072969 + 3 ^ 40 * 1814035 * 2
def baseEnd_1814035 : Nat := 310490626359638437806637

theorem tailTrace_1814035 : CollatzResearch.WordTrace tailWord_1814035 prefixEnd_1814035 310490626359638437806637 := by
  unfold tailWord_1814035
  simp only [CollatzResearch.WordTrace]
  refine ⟨66163291983068482357675559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44108861322045654905117039 66163291983068482357675559)
  ·
    refine ⟨99244937974602723536513339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66163291983068482357675559 99244937974602723536513339)
    ·
      refine ⟨148867406961904085304770009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99244937974602723536513339 148867406961904085304770009)
      ·
        refine ⟨111650555221428063978577507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148867406961904085304770009 111650555221428063978577507)
        ·
          refine ⟨167475832832142095967866261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111650555221428063978577507 167475832832142095967866261)
          ·
            refine ⟨7850429664006660748493731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167475832832142095967866261 7850429664006660748493731)
            ·
              refine ⟨11775644496009991122740597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850429664006660748493731 11775644496009991122740597)
              ·
                refine ⟨1103966671500936667756931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11775644496009991122740597 1103966671500936667756931)
                ·
                  refine ⟨1655950007251405001635397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1103966671500936667756931 1655950007251405001635397)
                  ·
                    refine ⟨310490626359638437806637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1655950007251405001635397 310490626359638437806637)
                    ·
                      rfl

theorem cell23_1814035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 4].length) (baseStart_1814035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814035 prefixEnd_1814035 := by exact prefixLift 1814035
  have htrace : WordTrace (prefixWord ++ tailWord_1814035) baseStart_1814035 baseEnd_1814035 := by
    simpa [prefixWord, tailWord_1814035, baseEnd_1814035] using wordTrace_append hprefix tailTrace_1814035
  have hstable : (prefixWord ++ tailWord_1814035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814035).length < 2 ^ (prefixWord ++ tailWord_1814035).sum := by decide
  have hdescent : baseEnd_1814035 < baseStart_1814035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814048 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 8]
def baseStart_1814048 : Nat := 118140960795 + 1814048 * 2 ^ 59
def prefixEnd_1814048 : Nat := 4983230072969 + 3 ^ 40 * 1814048 * 2
def baseEnd_1814048 : Nat := 103497617147491529173039

theorem tailTrace_1814048 : CollatzResearch.WordTrace tailWord_1814048 prefixEnd_1814048 103497617147491529173039 := by
  unfold tailWord_1814048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33081883066010692788949399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44109177421347590385265865 33081883066010692788949399)
  ·
    refine ⟨49622824599016039183424099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33081883066010692788949399 49622824599016039183424099)
    ·
      refine ⟨74434236898524058775136149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49622824599016039183424099 74434236898524058775136149)
      ·
        refine ⟨3489104854618315255084507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74434236898524058775136149 3489104854618315255084507)
        ·
          refine ⟨5233657281927472882626761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489104854618315255084507 5233657281927472882626761)
          ·
            refine ⟨3925242961445604661970071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233657281927472882626761 3925242961445604661970071)
            ·
              refine ⟨5887864442168406992955107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925242961445604661970071 5887864442168406992955107)
              ·
                refine ⟨8831796663252610489432661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887864442168406992955107 8831796663252610489432661)
                ·
                  refine ⟨103497617147491529173039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8831796663252610489432661 103497617147491529173039)
                  ·
                    rfl

theorem cell23_1814048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_1814048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814048 prefixEnd_1814048 := by exact prefixLift 1814048
  have htrace : WordTrace (prefixWord ++ tailWord_1814048) baseStart_1814048 baseEnd_1814048 := by
    simpa [prefixWord, tailWord_1814048, baseEnd_1814048] using wordTrace_append hprefix tailTrace_1814048
  have hstable : (prefixWord ++ tailWord_1814048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814048).length < 2 ^ (prefixWord ++ tailWord_1814048).sum := by decide
  have hdescent : baseEnd_1814048 < baseStart_1814048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814085 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_1814085 : Nat := 118140960795 + 1814085 * 2 ^ 59
def prefixEnd_1814085 : Nat := 4983230072969 + 3 ^ 40 * 1814085 * 2
def baseEnd_1814085 : Nat := 931497553111640117794681

theorem tailTrace_1814085 : CollatzResearch.WordTrace tailWord_1814085 prefixEnd_1814085 931497553111640117794681 := by
  unfold tailWord_1814085
  simp only [CollatzResearch.WordTrace]
  refine ⟨66165115632887340896995709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44110077088591560597997139 66165115632887340896995709)
  ·
    refine ⟨24811918362332752836373391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66165115632887340896995709 24811918362332752836373391)
    ·
      refine ⟨37217877543499129254560087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24811918362332752836373391 37217877543499129254560087)
      ·
        refine ⟨55826816315248693881840131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37217877543499129254560087 55826816315248693881840131)
        ·
          refine ⟨83740224472873040822760197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55826816315248693881840131 83740224472873040822760197)
          ·
            refine ⟨15701292088663695154267537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83740224472873040822760197 15701292088663695154267537)
            ·
              refine ⟨11775969066497771365700653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15701292088663695154267537 11775969066497771365700653)
              ·
                refine ⟨4415988399936664262137745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11775969066497771365700653 4415988399936664262137745)
                ·
                  refine ⟨3311991299952498196603309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415988399936664262137745 3311991299952498196603309)
                  ·
                    refine ⟨1241996737482186823726241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3311991299952498196603309 1241996737482186823726241)
                    ·
                      refine ⟨931497553111640117794681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1241996737482186823726241 931497553111640117794681)
                      ·
                        rfl

theorem cell23_1814085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_1814085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814085 prefixEnd_1814085 := by exact prefixLift 1814085
  have htrace : WordTrace (prefixWord ++ tailWord_1814085) baseStart_1814085 baseEnd_1814085 := by
    simpa [prefixWord, tailWord_1814085, baseEnd_1814085] using wordTrace_append hprefix tailTrace_1814085
  have hstable : (prefixWord ++ tailWord_1814085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814085).length < 2 ^ (prefixWord ++ tailWord_1814085).sum := by decide
  have hdescent : baseEnd_1814085 < baseStart_1814085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814091 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 3, 6]
def baseStart_1814091 : Nat := 118140960795 + 1814091 * 2 ^ 59
def prefixEnd_1814091 : Nat := 4983230072969 + 3 ^ 40 * 1814091 * 2
def baseEnd_1814091 : Nat := 310500211331855698106551

theorem tailTrace_1814091 : CollatzResearch.WordTrace tailWord_1814091 prefixEnd_1814091 310500211331855698106551 := by
  unfold tailWord_1814091
  simp only [CollatzResearch.WordTrace]
  refine ⟨66165334470865603921714127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44110222980577069281142751 66165334470865603921714127)
  ·
    refine ⟨99248001706298405882571191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66165334470865603921714127 99248001706298405882571191)
    ·
      refine ⟨148872002559447608823856787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99248001706298405882571191 148872002559447608823856787)
      ·
        refine ⟨223308003839171413235785181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148872002559447608823856787 223308003839171413235785181)
        ·
          refine ⟨83740501439689279963419443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223308003839171413235785181 83740501439689279963419443)
          ·
            refine ⟨125610752159533919945129165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83740501439689279963419443 125610752159533919945129165)
            ·
              refine ⟨47104032059825219979423437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125610752159533919945129165 47104032059825219979423437)
              ·
                refine ⟨17664012022434457492283789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47104032059825219979423437 17664012022434457492283789)
                ·
                  refine ⟨6624004508412921559606421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17664012022434457492283789 6624004508412921559606421)
                  ·
                    refine ⟨310500211331855698106551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6624004508412921559606421 310500211331855698106551)
                    ·
                      rfl

theorem cell23_1814091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_1814091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814091 prefixEnd_1814091 := by exact prefixLift 1814091
  have htrace : WordTrace (prefixWord ++ tailWord_1814091) baseStart_1814091 baseEnd_1814091 := by
    simpa [prefixWord, tailWord_1814091, baseEnd_1814091] using wordTrace_append hprefix tailTrace_1814091
  have hstable : (prefixWord ++ tailWord_1814091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814091).length < 2 ^ (prefixWord ++ tailWord_1814091).sum := by decide
  have hdescent : baseEnd_1814091 < baseStart_1814091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814121 : List Nat := [1, 2, 1, 1, 1, 4, 3, 10]
def baseStart_1814121 : Nat := 118140960795 + 1814121 * 2 ^ 59
def prefixEnd_1814121 : Nat := 4983230072969 + 3 ^ 40 * 1814121 * 2
def baseEnd_1814121 : Nat := 34500594015377850997945

theorem tailTrace_1814121 : CollatzResearch.WordTrace tailWord_1814121 prefixEnd_1814121 34500594015377850997945 := by
  unfold tailWord_1814121
  simp only [CollatzResearch.WordTrace]
  refine ⟨66166428660756919045306217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44110952440504612696870811 66166428660756919045306217)
  ·
    refine ⟨49624821495567689283979663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66166428660756919045306217 49624821495567689283979663)
    ·
      refine ⟨74437232243351533925969495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49624821495567689283979663 74437232243351533925969495)
      ·
        refine ⟨111655848365027300888954243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74437232243351533925969495 111655848365027300888954243)
        ·
          refine ⟨167483772547540951333431365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111655848365027300888954243 167483772547540951333431365)
          ·
            refine ⟨31403207352663928375018381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167483772547540951333431365 31403207352663928375018381)
            ·
              refine ⟨11776202757248973140631893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31403207352663928375018381 11776202757248973140631893)
              ·
                refine ⟨34500594015377850997945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11776202757248973140631893 34500594015377850997945)
                ·
                  rfl

theorem cell23_1814121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 10].length) (baseStart_1814121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814121 prefixEnd_1814121 := by exact prefixLift 1814121
  have htrace : WordTrace (prefixWord ++ tailWord_1814121) baseStart_1814121 baseEnd_1814121 := by
    simpa [prefixWord, tailWord_1814121, baseEnd_1814121] using wordTrace_append hprefix tailTrace_1814121
  have hstable : (prefixWord ++ tailWord_1814121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814121).length < 2 ^ (prefixWord ++ tailWord_1814121).sum := by decide
  have hdescent : baseEnd_1814121 < baseStart_1814121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814128 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1814128 : Nat := 118140960795 + 1814128 * 2 ^ 59
def prefixEnd_1814128 : Nat := 4983230072969 + 3 ^ 40 * 1814128 * 2
def baseEnd_1814128 : Nat := 931519632779783449556983

theorem tailTrace_1814128 : CollatzResearch.WordTrace tailWord_1814128 prefixEnd_1814128 931519632779783449556983 := by
  unfold tailWord_1814128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33083341985865779620405519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44111122647821039493874025 33083341985865779620405519)
  ·
    refine ⟨49625012978798669430608279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33083341985865779620405519 49625012978798669430608279)
    ·
      refine ⟨74437519468198004145912419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49625012978798669430608279 74437519468198004145912419)
      ·
        refine ⟨111656279202297006218868629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74437519468198004145912419 111656279202297006218868629)
        ·
          refine ⟨5233888087607672166509467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111656279202297006218868629 5233888087607672166509467)
          ·
            refine ⟨7850832131411508249764201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233888087607672166509467 7850832131411508249764201)
            ·
              refine ⟨5888124098558631187323151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7850832131411508249764201 5888124098558631187323151)
              ·
                refine ⟨8832186147837946780984727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888124098558631187323151 8832186147837946780984727)
                ·
                  refine ⟨13248279221756920171477091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832186147837946780984727 13248279221756920171477091)
                  ·
                    refine ⟨19872418832635380257215637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13248279221756920171477091 19872418832635380257215637)
                    ·
                      refine ⟨931519632779783449556983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19872418832635380257215637 931519632779783449556983)
                      ·
                        rfl

theorem cell23_1814128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1814128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814128 prefixEnd_1814128 := by exact prefixLift 1814128
  have htrace : WordTrace (prefixWord ++ tailWord_1814128) baseStart_1814128 baseEnd_1814128 := by
    simpa [prefixWord, tailWord_1814128, baseEnd_1814128] using wordTrace_append hprefix tailTrace_1814128
  have hstable : (prefixWord ++ tailWord_1814128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814128).length < 2 ^ (prefixWord ++ tailWord_1814128).sum := by decide
  have hdescent : baseEnd_1814128 < baseStart_1814128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814145 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1814145 : Nat := 118140960795 + 1814145 * 2 ^ 59
def prefixEnd_1814145 : Nat := 4983230072969 + 3 ^ 40 * 1814145 * 2
def baseEnd_1814145 : Nat := 931528361950909883044405

theorem tailTrace_1814145 : CollatzResearch.WordTrace tailWord_1814145 prefixEnd_1814145 931528361950909883044405 := by
  unfold tailWord_1814145
  simp only [CollatzResearch.WordTrace]
  refine ⟨66167304012669971144179889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44111536008446647429453259 66167304012669971144179889)
  ·
    refine ⟨49625478009502478358134917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66167304012669971144179889 49625478009502478358134917)
    ·
      refine ⟨9304777126781714692150297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49625478009502478358134917 9304777126781714692150297)
      ·
        refine ⟨6978582845086286019112723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9304777126781714692150297 6978582845086286019112723)
        ·
          refine ⟨10467874267629429028669085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978582845086286019112723 10467874267629429028669085)
          ·
            refine ⟨3925452850361035885750907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10467874267629429028669085 3925452850361035885750907)
            ·
              refine ⟨5888179275541553828626361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925452850361035885750907 5888179275541553828626361)
              ·
                refine ⟨4416134456656165371469771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5888179275541553828626361 4416134456656165371469771)
                ·
                  refine ⟨6624201684984248057204657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416134456656165371469771 6624201684984248057204657)
                  ·
                    refine ⟨4968151263738186042903493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624201684984248057204657 4968151263738186042903493)
                    ·
                      refine ⟨931528361950909883044405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4968151263738186042903493 931528361950909883044405)
                      ·
                        rfl

theorem cell23_1814145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1814145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814145 prefixEnd_1814145 := by exact prefixLift 1814145
  have htrace : WordTrace (prefixWord ++ tailWord_1814145) baseStart_1814145 baseEnd_1814145 := by
    simpa [prefixWord, tailWord_1814145, baseEnd_1814145] using wordTrace_append hprefix tailTrace_1814145
  have hstable : (prefixWord ++ tailWord_1814145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814145).length < 2 ^ (prefixWord ++ tailWord_1814145).sum := by decide
  have hdescent : baseEnd_1814145 < baseStart_1814145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814149 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 1, 2, 2]
def baseStart_1814149 : Nat := 118140960795 + 1814149 * 2 ^ 59
def prefixEnd_1814149 : Nat := 4983230072969 + 3 ^ 40 * 1814149 * 2
def baseEnd_1814149 : Nat := 931530415873527867394387

theorem tailTrace_1814149 : CollatzResearch.WordTrace tailWord_1814149 prefixEnd_1814149 931530415873527867394387 := by
  unfold tailWord_1814149
  simp only [CollatzResearch.WordTrace]
  refine ⟨66167449904655479827325501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44111633269770319884883667 66167449904655479827325501)
  ·
    refine ⟨24812793714245804935247063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66167449904655479827325501 24812793714245804935247063)
    ·
      refine ⟨37219190571368707402870595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24812793714245804935247063 37219190571368707402870595)
      ·
        refine ⟨55828785857053061104305893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37219190571368707402870595 55828785857053061104305893)
        ·
          refine ⟨10467897348197448957057355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55828785857053061104305893 10467897348197448957057355)
          ·
            refine ⟨15701846022296173435586033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467897348197448957057355 15701846022296173435586033)
            ·
              refine ⟨11776384516722130076689525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15701846022296173435586033 11776384516722130076689525)
              ·
                refine ⟨1104036048442699694689643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11776384516722130076689525 1104036048442699694689643)
                ·
                  refine ⟨1656054072664049542034465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104036048442699694689643 1656054072664049542034465)
                  ·
                    refine ⟨1242040554498037156525849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1656054072664049542034465 1242040554498037156525849)
                    ·
                      refine ⟨931530415873527867394387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242040554498037156525849 931530415873527867394387)
                      ·
                        rfl

theorem cell23_1814149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_1814149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814149 prefixEnd_1814149 := by exact prefixLift 1814149
  have htrace : WordTrace (prefixWord ++ tailWord_1814149) baseStart_1814149 baseEnd_1814149 := by
    simpa [prefixWord, tailWord_1814149, baseEnd_1814149] using wordTrace_append hprefix tailTrace_1814149
  have hstable : (prefixWord ++ tailWord_1814149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814149).length < 2 ^ (prefixWord ++ tailWord_1814149).sum := by decide
  have hdescent : baseEnd_1814149 < baseStart_1814149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814165 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_1814165 : Nat := 118140960795 + 1814165 * 2 ^ 59
def prefixEnd_1814165 : Nat := 4983230072969 + 3 ^ 40 * 1814165 * 2
def baseEnd_1814165 : Nat := 931538631563999804794313

theorem tailTrace_1814165 : CollatzResearch.WordTrace tailWord_1814165 prefixEnd_1814165 931538631563999804794313 := by
  unfold tailWord_1814165
  simp only [CollatzResearch.WordTrace]
  refine ⟨66168033472597514559907949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44112022315065009706605299 66168033472597514559907949)
  ·
    refine ⟨24813012552224067959965481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66168033472597514559907949 24813012552224067959965481)
    ·
      refine ⟨18609759414168050969974111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24813012552224067959965481 18609759414168050969974111)
      ·
        refine ⟨27914639121252076454961167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18609759414168050969974111 27914639121252076454961167)
        ·
          refine ⟨41871958681878114682441751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27914639121252076454961167 41871958681878114682441751)
          ·
            refine ⟨62807938022817172023662627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41871958681878114682441751 62807938022817172023662627)
            ·
              refine ⟨94211907034225758035493941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62807938022817172023662627 94211907034225758035493941)
              ·
                refine ⟨8832366284458664815827557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94211907034225758035493941 8832366284458664815827557)
                ·
                  refine ⟨1656068678335999652967667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8832366284458664815827557 1656068678335999652967667)
                  ·
                    refine ⟨2484103017503999479451501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656068678335999652967667 2484103017503999479451501)
                    ·
                      refine ⟨931538631563999804794313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2484103017503999479451501 931538631563999804794313)
                      ·
                        rfl

theorem cell23_1814165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_1814165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814165 prefixEnd_1814165 := by exact prefixLift 1814165
  have htrace : WordTrace (prefixWord ++ tailWord_1814165) baseStart_1814165 baseEnd_1814165 := by
    simpa [prefixWord, tailWord_1814165, baseEnd_1814165] using wordTrace_append hprefix tailTrace_1814165
  have hstable : (prefixWord ++ tailWord_1814165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814165).length < 2 ^ (prefixWord ++ tailWord_1814165).sum := by decide
  have hdescent : baseEnd_1814165 < baseStart_1814165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814168 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_1814168 : Nat := 118140960795 + 1814168 * 2 ^ 59
def prefixEnd_1814168 : Nat := 4983230072969 + 3 ^ 40 * 1814168 * 2
def baseEnd_1814168 : Nat := 310513390668654431018933

theorem tailTrace_1814168 : CollatzResearch.WordTrace tailWord_1814168 prefixEnd_1814168 310513390668654431018933 := by
  unfold tailWord_1814168
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084071445793323036133579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44112095261057764048178105 33084071445793323036133579)
  ·
    refine ⟨49626107168689984554200369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33084071445793323036133579 49626107168689984554200369)
    ·
      refine ⟨37219580376517488415650277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49626107168689984554200369 37219580376517488415650277)
      ·
        refine ⟨6978671320597029077934427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37219580376517488415650277 6978671320597029077934427)
        ·
          refine ⟨10468006980895543616901641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978671320597029077934427 10468006980895543616901641)
          ·
            refine ⟨7851005235671657712676231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10468006980895543616901641 7851005235671657712676231)
            ·
              refine ⟨11776507853507486569014347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851005235671657712676231 11776507853507486569014347)
              ·
                refine ⟨17664761780261229853521521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11776507853507486569014347 17664761780261229853521521)
                ·
                  refine ⟨13248571335195922390141141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17664761780261229853521521 13248571335195922390141141)
                  ·
                    refine ⟨310513390668654431018933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13248571335195922390141141 310513390668654431018933)
                    ·
                      rfl

theorem cell23_1814168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_1814168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814168 prefixEnd_1814168 := by exact prefixLift 1814168
  have htrace : WordTrace (prefixWord ++ tailWord_1814168) baseStart_1814168 baseEnd_1814168 := by
    simpa [prefixWord, tailWord_1814168, baseEnd_1814168] using wordTrace_append hprefix tailTrace_1814168
  have hstable : (prefixWord ++ tailWord_1814168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814168).length < 2 ^ (prefixWord ++ tailWord_1814168).sum := by decide
  have hdescent : baseEnd_1814168 < baseStart_1814168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814172 : List Nat := [2, 2, 3, 2, 4, 1, 1, 8]
def baseStart_1814172 : Nat := 118140960795 + 1814172 * 2 ^ 59
def prefixEnd_1814172 : Nat := 4983230072969 + 3 ^ 40 * 1814172 * 2
def baseEnd_1814172 : Nat := 34501563923280788052103

theorem tailTrace_1814172 : CollatzResearch.WordTrace tailWord_1814172 prefixEnd_1814172 34501563923280788052103 := by
  unfold tailWord_1814172
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084144391786077377706385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44112192522381436503608513 33084144391786077377706385)
  ·
    refine ⟨24813108293839558033279789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33084144391786077377706385 24813108293839558033279789)
    ·
      refine ⟨9304915610189834262479921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24813108293839558033279789 9304915610189834262479921)
      ·
        refine ⟨6978686707642375696859941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9304915610189834262479921 6978686707642375696859941)
        ·
          refine ⟨1308503757682945443161239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6978686707642375696859941 1308503757682945443161239)
          ·
            refine ⟨1962755636524418164741859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308503757682945443161239 1962755636524418164741859)
            ·
              refine ⟨2944133454786627247112789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962755636524418164741859 2944133454786627247112789)
              ·
                refine ⟨34501563923280788052103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2944133454786627247112789 34501563923280788052103)
                ·
                  rfl

theorem cell23_1814172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 8].length) (baseStart_1814172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814172 prefixEnd_1814172 := by exact prefixLift 1814172
  have htrace : WordTrace (prefixWord ++ tailWord_1814172) baseStart_1814172 baseEnd_1814172 := by
    simpa [prefixWord, tailWord_1814172, baseEnd_1814172] using wordTrace_append hprefix tailTrace_1814172
  have hstable : (prefixWord ++ tailWord_1814172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814172).length < 2 ^ (prefixWord ++ tailWord_1814172).sum := by decide
  have hdescent : baseEnd_1814172 < baseStart_1814172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814208 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1814208 : Nat := 118140960795 + 1814208 * 2 ^ 59
def prefixEnd_1814208 : Nat := 4983230072969 + 3 ^ 40 * 1814208 * 2
def baseEnd_1814208 : Nat := 931560711232143136556615

theorem tailTrace_1814208 : CollatzResearch.WordTrace tailWord_1814208 prefixEnd_1814208 931560711232143136556615 := by
  unfold tailWord_1814208
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084800905720866451861639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44113067874294488602482185 33084800905720866451861639)
  ·
    refine ⟨49627201358581299677792459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33084800905720866451861639 49627201358581299677792459)
    ·
      refine ⟨74440802037871949516688689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49627201358581299677792459 74440802037871949516688689)
      ·
        refine ⟨55830601528403962137516517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74440802037871949516688689 55830601528403962137516517)
        ·
          refine ⟨10468237786575742900784347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55830601528403962137516517 10468237786575742900784347)
          ·
            refine ⟨15702356679863614351176521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468237786575742900784347 15702356679863614351176521)
            ·
              refine ⟨11776767509897710763382391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15702356679863614351176521 11776767509897710763382391)
              ·
                refine ⟨17665151264846566145073587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11776767509897710763382391 17665151264846566145073587)
                ·
                  refine ⟨26497726897269849217610381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17665151264846566145073587 26497726897269849217610381)
                  ·
                    refine ⟨9936647586476193456603893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26497726897269849217610381 9936647586476193456603893)
                    ·
                      refine ⟨931560711232143136556615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9936647586476193456603893 931560711232143136556615)
                      ·
                        rfl

theorem cell23_1814208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1814208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814208 prefixEnd_1814208 := by exact prefixLift 1814208
  have htrace : WordTrace (prefixWord ++ tailWord_1814208) baseStart_1814208 baseEnd_1814208 := by
    simpa [prefixWord, tailWord_1814208, baseEnd_1814208] using wordTrace_append hprefix tailTrace_1814208
  have hstable : (prefixWord ++ tailWord_1814208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814208).length < 2 ^ (prefixWord ++ tailWord_1814208).sum := by decide
  have hdescent : baseEnd_1814208 < baseStart_1814208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814210 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1814210 : Nat := 118140960795 + 1814210 * 2 ^ 59
def prefixEnd_1814210 : Nat := 4983230072969 + 3 ^ 40 * 1814210 * 2
def baseEnd_1814210 : Nat := 310520579397817376243869

theorem tailTrace_1814210 : CollatzResearch.WordTrace tailWord_1814210 prefixEnd_1814210 310520579397817376243869 := by
  unfold tailWord_1814210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16542418689358621811324021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44113116504956324830197389 16542418689358621811324021)
  ·
    refine ⟨1550851752127370794811627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16542418689358621811324021 1550851752127370794811627)
    ·
      refine ⟨2326277628191056192217441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550851752127370794811627 2326277628191056192217441)
      ·
        refine ⟨1744708221143292144163081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326277628191056192217441 1744708221143292144163081)
        ·
          refine ⟨1308531165857469108122311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744708221143292144163081 1308531165857469108122311)
          ·
            refine ⟨1962796748786203662183467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308531165857469108122311 1962796748786203662183467)
            ·
              refine ⟨2944195123179305493275201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962796748786203662183467 2944195123179305493275201)
              ·
                refine ⟨2208146342384479119956401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944195123179305493275201 2208146342384479119956401)
                ·
                  refine ⟨1656109756788359339967301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208146342384479119956401 1656109756788359339967301)
                  ·
                    refine ⟨310520579397817376243869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1656109756788359339967301 310520579397817376243869)
                    ·
                      rfl

theorem cell23_1814210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1814210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814210 prefixEnd_1814210 := by exact prefixLift 1814210
  have htrace : WordTrace (prefixWord ++ tailWord_1814210) baseStart_1814210 baseEnd_1814210 := by
    simpa [prefixWord, tailWord_1814210, baseEnd_1814210] using wordTrace_append hprefix tailTrace_1814210
  have hstable : (prefixWord ++ tailWord_1814210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814210).length < 2 ^ (prefixWord ++ tailWord_1814210).sum := by decide
  have hdescent : baseEnd_1814210 < baseStart_1814210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814265 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 7, 2]
def baseStart_1814265 : Nat := 118140960795 + 1814265 * 2 ^ 59
def prefixEnd_1814265 : Nat := 4983230072969 + 3 ^ 40 * 1814265 * 2
def baseEnd_1814265 : Nat := 931589979629449413543853

theorem tailTrace_1814265 : CollatzResearch.WordTrace tailWord_1814265 prefixEnd_1814265 931589979629449413543853 := by
  unfold tailWord_1814265
  simp only [CollatzResearch.WordTrace]
  refine ⟨66171680772235231638548249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44114453848156821092365499 66171680772235231638548249)
  ·
    refine ⟨49628760579176423728911187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66171680772235231638548249 49628760579176423728911187)
    ·
      refine ⟨74443140868764635593366781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49628760579176423728911187 74443140868764635593366781)
      ·
        refine ⟨27916177825786738347512543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74443140868764635593366781 27916177825786738347512543)
        ·
          refine ⟨41874266738680107521268815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27916177825786738347512543 41874266738680107521268815)
          ·
            refine ⟨62811400108020161281903223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41874266738680107521268815 62811400108020161281903223)
            ·
              refine ⟨94217100162030241922854835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62811400108020161281903223 94217100162030241922854835)
              ·
                refine ⟨141325650243045362884282253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94217100162030241922854835 141325650243045362884282253)
                ·
                  refine ⟨52997118841142011081605845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141325650243045362884282253 52997118841142011081605845)
                  ·
                    refine ⟨1242119972839265884725137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52997118841142011081605845 1242119972839265884725137)
                    ·
                      refine ⟨931589979629449413543853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242119972839265884725137 931589979629449413543853)
                      ·
                        rfl

theorem cell23_1814265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_1814265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814265 prefixEnd_1814265 := by exact prefixLift 1814265
  have htrace : WordTrace (prefixWord ++ tailWord_1814265) baseStart_1814265 baseEnd_1814265 := by
    simpa [prefixWord, tailWord_1814265, baseEnd_1814265] using wordTrace_append hprefix tailTrace_1814265
  have hstable : (prefixWord ++ tailWord_1814265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814265).length < 2 ^ (prefixWord ++ tailWord_1814265).sum := by decide
  have hdescent : baseEnd_1814265 < baseStart_1814265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814279 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 7]
def baseStart_1814279 : Nat := 118140960795 + 1814279 * 2 ^ 59
def prefixEnd_1814279 : Nat := 4983230072969 + 3 ^ 40 * 1814279 * 2
def baseEnd_1814279 : Nat := 103510796484290262085421

theorem tailTrace_1814279 : CollatzResearch.WordTrace tailWord_1814279 prefixEnd_1814279 103510796484290262085421 := by
  unfold tailWord_1814279
  simp only [CollatzResearch.WordTrace]
  refine ⟨66172191394184512029557891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44114794262789674686371927 66172191394184512029557891)
  ·
    refine ⟨99258287091276768044336837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66172191394184512029557891 99258287091276768044336837)
    ·
      refine ⟨18610928829614394008313157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99258287091276768044336837 18610928829614394008313157)
      ·
        refine ⟨3489549155552698876558717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18610928829614394008313157 3489549155552698876558717)
        ·
          refine ⟨1308580933332262078709519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3489549155552698876558717 1308580933332262078709519)
          ·
            refine ⟨1962871399998393118064279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308580933332262078709519 1962871399998393118064279)
            ·
              refine ⟨2944307099997589677096419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962871399998393118064279 2944307099997589677096419)
              ·
                refine ⟨4416460649996384515644629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944307099997589677096419 4416460649996384515644629)
                ·
                  refine ⟨103510796484290262085421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4416460649996384515644629 103510796484290262085421)
                  ·
                    rfl

theorem cell23_1814279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 7].length) (baseStart_1814279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814279 prefixEnd_1814279 := by exact prefixLift 1814279
  have htrace : WordTrace (prefixWord ++ tailWord_1814279) baseStart_1814279 baseEnd_1814279 := by
    simpa [prefixWord, tailWord_1814279, baseEnd_1814279] using wordTrace_append hprefix tailTrace_1814279
  have hstable : (prefixWord ++ tailWord_1814279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814279).length < 2 ^ (prefixWord ++ tailWord_1814279).sum := by decide
  have hdescent : baseEnd_1814279 < baseStart_1814279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814290 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1814290 : Nat := 118140960795 + 1814290 * 2 ^ 59
def prefixEnd_1814290 : Nat := 4983230072969 + 3 ^ 40 * 1814290 * 2
def baseEnd_1814290 : Nat := 931602816645811815731239

theorem tailTrace_1814290 : CollatzResearch.WordTrace tailWord_1814290 prefixEnd_1814290 931602816645811815731239 := by
  unfold tailWord_1814290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16543148149286165227052081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44115061731429773938805549 16543148149286165227052081)
  ·
    refine ⟨12407361111964623920289061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16543148149286165227052081 12407361111964623920289061)
    ·
      refine ⟨2326380208493366985054199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12407361111964623920289061 2326380208493366985054199)
      ·
        refine ⟨3489570312740050477581299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2326380208493366985054199 3489570312740050477581299)
        ·
          refine ⟨5234355469110075716371949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489570312740050477581299 5234355469110075716371949)
          ·
            refine ⟨1962883300916278393639481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5234355469110075716371949 1962883300916278393639481)
            ·
              refine ⟨1472162475687208795229611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962883300916278393639481 1472162475687208795229611)
              ·
                refine ⟨2208243713530813192844417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472162475687208795229611 2208243713530813192844417)
                ·
                  refine ⟨1656182785148109894633313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208243713530813192844417 1656182785148109894633313)
                  ·
                    refine ⟨1242137088861082420974985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1656182785148109894633313 1242137088861082420974985)
                    ·
                      refine ⟨931602816645811815731239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242137088861082420974985 931602816645811815731239)
                      ·
                        rfl

theorem cell23_1814290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1814290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814290 prefixEnd_1814290 := by exact prefixLift 1814290
  have htrace : WordTrace (prefixWord ++ tailWord_1814290) baseStart_1814290 baseEnd_1814290 := by
    simpa [prefixWord, tailWord_1814290, baseEnd_1814290] using wordTrace_append hprefix tailTrace_1814290
  have hstable : (prefixWord ++ tailWord_1814290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814290).length < 2 ^ (prefixWord ++ tailWord_1814290).sum := by decide
  have hdescent : baseEnd_1814290 < baseStart_1814290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814312 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1814312 : Nat := 118140960795 + 1814312 * 2 ^ 59
def prefixEnd_1814312 : Nat := 4983230072969 + 3 ^ 40 * 1814312 * 2
def baseEnd_1814312 : Nat := 931614113220210729656137

theorem tailTrace_1814312 : CollatzResearch.WordTrace tailWord_1814312 prefixEnd_1814312 931614113220210729656137 := by
  unfold tailWord_1814312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086697501532479332754595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44115596668709972443672793 33086697501532479332754595)
  ·
    refine ⟨49630046252298718999131893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33086697501532479332754595 49630046252298718999131893)
    ·
      refine ⟨4652816836153004906168615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49630046252298718999131893 4652816836153004906168615)
      ·
        refine ⟨6979225254229507359252923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652816836153004906168615 6979225254229507359252923)
        ·
          refine ⟨10468837881344261038879385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979225254229507359252923 10468837881344261038879385)
          ·
            refine ⟨7851628411008195779159539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10468837881344261038879385 7851628411008195779159539)
            ·
              refine ⟨11777442616512293668739309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851628411008195779159539 11777442616512293668739309)
              ·
                refine ⟨4416540981192110125777241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11777442616512293668739309 4416540981192110125777241)
                ·
                  refine ⟨3312405735894082594332931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4416540981192110125777241 3312405735894082594332931)
                  ·
                    refine ⟨4968608603841123891499397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3312405735894082594332931 4968608603841123891499397)
                    ·
                      refine ⟨931614113220210729656137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4968608603841123891499397 931614113220210729656137)
                      ·
                        rfl

theorem cell23_1814312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1814312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814312 prefixEnd_1814312 := by exact prefixLift 1814312
  have htrace : WordTrace (prefixWord ++ tailWord_1814312) baseStart_1814312 baseEnd_1814312 := by
    simpa [prefixWord, tailWord_1814312, baseEnd_1814312] using wordTrace_append hprefix tailTrace_1814312
  have hstable : (prefixWord ++ tailWord_1814312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814312).length < 2 ^ (prefixWord ++ tailWord_1814312).sum := by decide
  have hdescent : baseEnd_1814312 < baseStart_1814312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814332 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1814332 : Nat := 118140960795 + 1814332 * 2 ^ 59
def prefixEnd_1814332 : Nat := 4983230072969 + 3 ^ 40 * 1814332 * 2
def baseEnd_1814332 : Nat := 931624382833300651406045

theorem tailTrace_1814332 : CollatzResearch.WordTrace tailWord_1814332 prefixEnd_1814332 931624382833300651406045 := by
  unfold tailWord_1814332
  simp only [CollatzResearch.WordTrace]
  refine ⟨33087062231496251040618625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44116082975328334720824833 33087062231496251040618625)
  ·
    refine ⟨24815296673622188280463969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33087062231496251040618625 24815296673622188280463969)
    ·
      refine ⟨18611472505216641210347977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24815296673622188280463969 18611472505216641210347977)
      ·
        refine ⟨13958604378912480907760983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18611472505216641210347977 13958604378912480907760983)
        ·
          refine ⟨20937906568368721361641475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13958604378912480907760983 20937906568368721361641475)
          ·
            refine ⟨31406859852553082042462213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20937906568368721361641475 31406859852553082042462213)
            ·
              refine ⟨5888786222353702882961665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31406859852553082042462213 5888786222353702882961665)
              ·
                refine ⟨4416589666765277162221249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5888786222353702882961665 4416589666765277162221249)
                ·
                  refine ⟨3312442250073957871665937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4416589666765277162221249 3312442250073957871665937)
                  ·
                    refine ⟨2484331687555468403749453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312442250073957871665937 2484331687555468403749453)
                    ·
                      refine ⟨931624382833300651406045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2484331687555468403749453 931624382833300651406045)
                      ·
                        rfl

theorem cell23_1814332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1814332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814332 prefixEnd_1814332 := by exact prefixLift 1814332
  have htrace : WordTrace (prefixWord ++ tailWord_1814332) baseStart_1814332 baseEnd_1814332 := by
    simpa [prefixWord, tailWord_1814332, baseEnd_1814332] using wordTrace_append hprefix tailTrace_1814332
  have hstable : (prefixWord ++ tailWord_1814332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814332).length < 2 ^ (prefixWord ++ tailWord_1814332).sum := by decide
  have hdescent : baseEnd_1814332 < baseStart_1814332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814339 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 1, 4]
def baseStart_1814339 : Nat := 118140960795 + 1814339 * 2 ^ 59
def prefixEnd_1814339 : Nat := 4983230072969 + 3 ^ 40 * 1814339 * 2
def baseEnd_1814339 : Nat := 310542659065960708006171

theorem tailTrace_1814339 : CollatzResearch.WordTrace tailWord_1814339 prefixEnd_1814339 310542659065960708006171 := by
  unfold tailWord_1814339
  simp only [CollatzResearch.WordTrace]
  refine ⟨66174379773967142276742071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44116253182644761517828047 66174379773967142276742071)
  ·
    refine ⟨99261569660950713415113107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66174379773967142276742071 99261569660950713415113107)
    ·
      refine ⟨148892354491426070122669661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99261569660950713415113107 148892354491426070122669661)
      ·
        refine ⟨55834632934284776296001123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148892354491426070122669661 55834632934284776296001123)
        ·
          refine ⟨83751949401427164444001685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55834632934284776296001123 83751949401427164444001685)
          ·
            refine ⟨3925872628191898333312579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83751949401427164444001685 3925872628191898333312579)
            ·
              refine ⟨5888808942287847499968869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925872628191898333312579 5888808942287847499968869)
              ·
                refine ⟨1104151676678971406244163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5888808942287847499968869 1104151676678971406244163)
                ·
                  refine ⟨1656227515018457109366245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104151676678971406244163 1656227515018457109366245)
                  ·
                    refine ⟨310542659065960708006171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1656227515018457109366245 310542659065960708006171)
                    ·
                      rfl

theorem cell23_1814339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 4].length) (baseStart_1814339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814339 prefixEnd_1814339 := by exact prefixLift 1814339
  have htrace : WordTrace (prefixWord ++ tailWord_1814339) baseStart_1814339 baseEnd_1814339 := by
    simpa [prefixWord, tailWord_1814339, baseEnd_1814339] using wordTrace_append hprefix tailTrace_1814339
  have hstable : (prefixWord ++ tailWord_1814339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814339).length < 2 ^ (prefixWord ++ tailWord_1814339).sum := by decide
  have hdescent : baseEnd_1814339 < baseStart_1814339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814389 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1814389 : Nat := 118140960795 + 1814389 * 2 ^ 59
def prefixEnd_1814389 : Nat := 4983230072969 + 3 ^ 40 * 1814389 * 2
def baseEnd_1814389 : Nat := 931653651230606928393283

theorem tailTrace_1814389 : CollatzResearch.WordTrace tailWord_1814389 prefixEnd_1814389 931653651230606928393283 := by
  unfold tailWord_1814389
  simp only [CollatzResearch.WordTrace]
  refine ⟨66176203423786000816062221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44117468949190667210708147 66176203423786000816062221)
  ·
    refine ⟨24816076283919750306023333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66176203423786000816062221 24816076283919750306023333)
    ·
      refine ⟨4653014303234953182379375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24816076283919750306023333 4653014303234953182379375)
      ·
        refine ⟨6979521454852429773569063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4653014303234953182379375 6979521454852429773569063)
        ·
          refine ⟨10469282182278644660353595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979521454852429773569063 10469282182278644660353595)
          ·
            refine ⟨15703923273417966990530393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469282182278644660353595 15703923273417966990530393)
            ·
              refine ⟨11777942455063475242897795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15703923273417966990530393 11777942455063475242897795)
              ·
                refine ⟨17666913682595212864346693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777942455063475242897795 17666913682595212864346693)
                ·
                  refine ⟨3312546315486602412065005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17666913682595212864346693 3312546315486602412065005)
                  ·
                    refine ⟨1242204868307475904524377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312546315486602412065005 1242204868307475904524377)
                    ·
                      refine ⟨931653651230606928393283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242204868307475904524377 931653651230606928393283)
                      ·
                        rfl

theorem cell23_1814389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1814389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814389 prefixEnd_1814389 := by exact prefixLift 1814389
  have htrace : WordTrace (prefixWord ++ tailWord_1814389) baseStart_1814389 baseEnd_1814389 := by
    simpa [prefixWord, tailWord_1814389, baseEnd_1814389] using wordTrace_append hprefix tailTrace_1814389
  have hstable : (prefixWord ++ tailWord_1814389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814389).length < 2 ^ (prefixWord ++ tailWord_1814389).sum := by decide
  have hdescent : baseEnd_1814389 < baseStart_1814389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814439 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1814439 : Nat := 118140960795 + 1814439 * 2 ^ 59
def prefixEnd_1814439 : Nat := 4983230072969 + 3 ^ 40 * 1814439 * 2
def baseEnd_1814439 : Nat := 931679325263331732768053

theorem tailTrace_1814439 : CollatzResearch.WordTrace tailWord_1814439 prefixEnd_1814439 931679325263331732768053 := by
  unfold tailWord_1814439
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178027073604859355382371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44118684715736572903588247 66178027073604859355382371)
  ·
    refine ⟨99267040610407289033073557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66178027073604859355382371 99267040610407289033073557)
    ·
      refine ⟨4653142528612841673425323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99267040610407289033073557 4653142528612841673425323)
      ·
        refine ⟨6979713792919262510137985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4653142528612841673425323 6979713792919262510137985)
        ·
          refine ⟨5234785344689446882603489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6979713792919262510137985 5234785344689446882603489)
          ·
            refine ⟨3926089008517085161952617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234785344689446882603489 3926089008517085161952617)
            ·
              refine ⟨2944566756387813871464463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926089008517085161952617 2944566756387813871464463)
              ·
                refine ⟨4416850134581720807196695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944566756387813871464463 4416850134581720807196695)
                ·
                  refine ⟨6625275201872581210795043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416850134581720807196695 6625275201872581210795043)
                  ·
                    refine ⟨9937912802808871816192565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6625275201872581210795043 9937912802808871816192565)
                    ·
                      refine ⟨931679325263331732768053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9937912802808871816192565 931679325263331732768053)
                      ·
                        rfl

theorem cell23_1814439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1814439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814439 prefixEnd_1814439 := by exact prefixLift 1814439
  have htrace : WordTrace (prefixWord ++ tailWord_1814439) baseStart_1814439 baseEnd_1814439 := by
    simpa [prefixWord, tailWord_1814439, baseEnd_1814439] using wordTrace_append hprefix tailTrace_1814439
  have hstable : (prefixWord ++ tailWord_1814439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814439).length < 2 ^ (prefixWord ++ tailWord_1814439).sum := by decide
  have hdescent : baseEnd_1814439 < baseStart_1814439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814453 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_1814453 : Nat := 118140960795 + 1814453 * 2 ^ 59
def prefixEnd_1814453 : Nat := 4983230072969 + 3 ^ 40 * 1814453 * 2
def baseEnd_1814453 : Nat := 931686513992494677992989

theorem tailTrace_1814453 : CollatzResearch.WordTrace tailWord_1814453 prefixEnd_1814453 931686513992494677992989 := by
  unfold tailWord_1814453
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178537695554139746392013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44119025130369426497594675 66178537695554139746392013)
  ·
    refine ⟨24816951635832802404897005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66178537695554139746392013 24816951635832802404897005)
    ·
      refine ⟨9306356863437300901836377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24816951635832802404897005 9306356863437300901836377)
      ·
        refine ⟨6979767647577975676377283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9306356863437300901836377 6979767647577975676377283)
        ·
          refine ⟨10469651471366963514565925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979767647577975676377283 10469651471366963514565925)
          ·
            refine ⟨1963059650881305658981111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10469651471366963514565925 1963059650881305658981111)
            ·
              refine ⟨2944589476321958488471667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963059650881305658981111 2944589476321958488471667)
              ·
                refine ⟨4416884214482937732707501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944589476321958488471667 4416884214482937732707501)
                ·
                  refine ⟨1656331580431101649765313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4416884214482937732707501 1656331580431101649765313)
                  ·
                    refine ⟨1242248685323326237323985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1656331580431101649765313 1242248685323326237323985)
                    ·
                      refine ⟨931686513992494677992989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242248685323326237323985 931686513992494677992989)
                      ·
                        rfl

theorem cell23_1814453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_1814453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814453 prefixEnd_1814453 := by exact prefixLift 1814453
  have htrace : WordTrace (prefixWord ++ tailWord_1814453) baseStart_1814453 baseEnd_1814453 := by
    simpa [prefixWord, tailWord_1814453, baseEnd_1814453] using wordTrace_append hprefix tailTrace_1814453
  have hstable : (prefixWord ++ tailWord_1814453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814453).length < 2 ^ (prefixWord ++ tailWord_1814453).sum := by decide
  have hdescent : baseEnd_1814453 < baseStart_1814453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814455 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 7]
def baseStart_1814455 : Nat := 118140960795 + 1814455 * 2 ^ 59
def prefixEnd_1814455 : Nat := 4983230072969 + 3 ^ 40 * 1814455 * 2
def baseEnd_1814455 : Nat := 310562513651267890055993

theorem tailTrace_1814455 : CollatzResearch.WordTrace tailWord_1814455 prefixEnd_1814455 310562513651267890055993 := by
  unfold tailWord_1814455
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178610641546894087964819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44119073761031262725309879 66178610641546894087964819)
  ·
    refine ⟨99267915962320341131947229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66178610641546894087964819 99267915962320341131947229)
    ·
      refine ⟨37225468485870127924480211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99267915962320341131947229 37225468485870127924480211)
      ·
        refine ⟨55838202728805191886720317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37225468485870127924480211 55838202728805191886720317)
        ·
          refine ⟨20939326023301946957520119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55838202728805191886720317 20939326023301946957520119)
          ·
            refine ⟨31408989034952920436280179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20939326023301946957520119 31408989034952920436280179)
            ·
              refine ⟨47113483552429380654420269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31408989034952920436280179 47113483552429380654420269)
              ·
                refine ⟨17667556332161017745407601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47113483552429380654420269 17667556332161017745407601)
                ·
                  refine ⟨13250667249120763309055701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17667556332161017745407601 13250667249120763309055701)
                  ·
                    refine ⟨310562513651267890055993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13250667249120763309055701 310562513651267890055993)
                    ·
                      rfl

theorem cell23_1814455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_1814455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814455 prefixEnd_1814455 := by exact prefixLift 1814455
  have htrace : WordTrace (prefixWord ++ tailWord_1814455) baseStart_1814455 baseEnd_1814455 := by
    simpa [prefixWord, tailWord_1814455, baseEnd_1814455] using wordTrace_append hprefix tailTrace_1814455
  have hstable : (prefixWord ++ tailWord_1814455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814455).length < 2 ^ (prefixWord ++ tailWord_1814455).sum := by decide
  have hdescent : baseEnd_1814455 < baseStart_1814455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814479 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 3, 3, 2]
def baseStart_1814479 : Nat := 118140960795 + 1814479 * 2 ^ 59
def prefixEnd_1814479 : Nat := 4983230072969 + 3 ^ 40 * 1814479 * 2
def baseEnd_1814479 : Nat := 931699864489511576267869

theorem tailTrace_1814479 : CollatzResearch.WordTrace tailWord_1814479 prefixEnd_1814479 931699864489511576267869 := by
  unfold tailWord_1814479
  simp only [CollatzResearch.WordTrace]
  refine ⟨66179485993459946186838491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44119657328973297457892327 66179485993459946186838491)
  ·
    refine ⟨99269228990189919280257737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66179485993459946186838491 99269228990189919280257737)
    ·
      refine ⟨74451921742642439460193303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99269228990189919280257737 74451921742642439460193303)
      ·
        refine ⟨111677882613963659190289955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74451921742642439460193303 111677882613963659190289955)
        ·
          refine ⟨167516823920945488785434933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111677882613963659190289955 167516823920945488785434933)
          ·
            refine ⟨15704702242588639573634525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167516823920945488785434933 15704702242588639573634525)
            ·
              refine ⟨5889263340970739840112947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15704702242588639573634525 5889263340970739840112947)
              ·
                refine ⟨8833895011456109760169421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889263340970739840112947 8833895011456109760169421)
                ·
                  refine ⟨3312710629296041160063533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8833895011456109760169421 3312710629296041160063533)
                  ·
                    refine ⟨1242266485986015435023825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3312710629296041160063533 1242266485986015435023825)
                    ·
                      refine ⟨931699864489511576267869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242266485986015435023825 931699864489511576267869)
                      ·
                        rfl

theorem cell23_1814479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3, 2].length) (baseStart_1814479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814479 prefixEnd_1814479 := by exact prefixLift 1814479
  have htrace : WordTrace (prefixWord ++ tailWord_1814479) baseStart_1814479 baseEnd_1814479 := by
    simpa [prefixWord, tailWord_1814479, baseEnd_1814479] using wordTrace_append hprefix tailTrace_1814479
  have hstable : (prefixWord ++ tailWord_1814479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814479).length < 2 ^ (prefixWord ++ tailWord_1814479).sum := by decide
  have hdescent : baseEnd_1814479 < baseStart_1814479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814503 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1814503 : Nat := 118140960795 + 1814503 * 2 ^ 59
def prefixEnd_1814503 : Nat := 4983230072969 + 3 ^ 40 * 1814503 * 2
def baseEnd_1814503 : Nat := 931712188025219482367759

theorem tailTrace_1814503 : CollatzResearch.WordTrace tailWord_1814503 prefixEnd_1814503 931712188025219482367759 := by
  unfold tailWord_1814503
  simp only [CollatzResearch.WordTrace]
  refine ⟨66180361345372998285712163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44120240896915332190474775 66180361345372998285712163)
  ·
    refine ⟨99270542018059497428568245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66180361345372998285712163 99270542018059497428568245)
    ·
      refine ⟨9306613314193077883928273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99270542018059497428568245 9306613314193077883928273)
      ·
        refine ⟨6979959985644808412946205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9306613314193077883928273 6979959985644808412946205)
        ·
          refine ⟨2617484994616803154854827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6979959985644808412946205 2617484994616803154854827)
          ·
            refine ⟨3926227491925204732282241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617484994616803154854827 3926227491925204732282241)
            ·
              refine ⟨2944670618943903549211681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926227491925204732282241 2944670618943903549211681)
              ·
                refine ⟨2208502964207927661908761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944670618943903549211681 2208502964207927661908761)
                ·
                  refine ⟨1656377223155945746431571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208502964207927661908761 1656377223155945746431571)
                  ·
                    refine ⟨2484565834733918619647357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656377223155945746431571 2484565834733918619647357)
                    ·
                      refine ⟨931712188025219482367759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2484565834733918619647357 931712188025219482367759)
                      ·
                        rfl

theorem cell23_1814503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1814503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814503 prefixEnd_1814503 := by exact prefixLift 1814503
  have htrace : WordTrace (prefixWord ++ tailWord_1814503) baseStart_1814503 baseEnd_1814503 := by
    simpa [prefixWord, tailWord_1814503, baseEnd_1814503] using wordTrace_append hprefix tailTrace_1814503
  have hstable : (prefixWord ++ tailWord_1814503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814503).length < 2 ^ (prefixWord ++ tailWord_1814503).sum := by decide
  have hdescent : baseEnd_1814503 < baseStart_1814503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814512 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_1814512 : Nat := 118140960795 + 1814512 * 2 ^ 59
def prefixEnd_1814512 : Nat := 4983230072969 + 3 ^ 40 * 1814512 * 2
def baseEnd_1814512 : Nat := 931716809351109947155217

theorem tailTrace_1814512 : CollatzResearch.WordTrace tailWord_1814512 prefixEnd_1814512 931716809351109947155217 := by
  unfold tailWord_1814512
  simp only [CollatzResearch.WordTrace]
  refine ⟨33090344801170196411394895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44120459734893595215193193 33090344801170196411394895)
  ·
    refine ⟨49635517201755294617092343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33090344801170196411394895 49635517201755294617092343)
    ·
      refine ⟨74453275802632941925638515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49635517201755294617092343 74453275802632941925638515)
      ·
        refine ⟨111679913703949412888457773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74453275802632941925638515 111679913703949412888457773)
        ·
          refine ⟨41879967638981029833171665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111679913703949412888457773 41879967638981029833171665)
          ·
            refine ⟨31409975729235772374878749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41879967638981029833171665 31409975729235772374878749)
            ·
              refine ⟨11778740898463414640579531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31409975729235772374878749 11778740898463414640579531)
              ·
                refine ⟨17668111347695121960869297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778740898463414640579531 17668111347695121960869297)
                ·
                  refine ⟨13251083510771341470651973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17668111347695121960869297 13251083510771341470651973)
                  ·
                    refine ⟨2484578158269626525747245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13251083510771341470651973 2484578158269626525747245)
                    ·
                      refine ⟨931716809351109947155217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2484578158269626525747245 931716809351109947155217)
                      ·
                        rfl

theorem cell23_1814512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_1814512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814512 prefixEnd_1814512 := by exact prefixLift 1814512
  have htrace : WordTrace (prefixWord ++ tailWord_1814512) baseStart_1814512 baseEnd_1814512 := by
    simpa [prefixWord, tailWord_1814512, baseEnd_1814512] using wordTrace_append hprefix tailTrace_1814512
  have hstable : (prefixWord ++ tailWord_1814512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814512).length < 2 ^ (prefixWord ++ tailWord_1814512).sum := by decide
  have hdescent : baseEnd_1814512 < baseStart_1814512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814515 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 11]
def baseStart_1814515 : Nat := 118140960795 + 1814515 * 2 ^ 59
def prefixEnd_1814515 : Nat := 4983230072969 + 3 ^ 40 * 1814515 * 2
def baseEnd_1814515 : Nat := 103524261088119270601967

theorem tailTrace_1814515 : CollatzResearch.WordTrace tailWord_1814515 prefixEnd_1814515 103524261088119270601967 := by
  unfold tailWord_1814515
  simp only [CollatzResearch.WordTrace]
  refine ⟨66180799021329524335148999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44120532680886349556765999 66180799021329524335148999)
  ·
    refine ⟨99271198531994286502723499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66180799021329524335148999 99271198531994286502723499)
    ·
      refine ⟨148906797797991429754085249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99271198531994286502723499 148906797797991429754085249)
      ·
        refine ⟨111680098348493572315563937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148906797797991429754085249 111680098348493572315563937)
        ·
          refine ⟨83760073761370179236672953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111680098348493572315563937 83760073761370179236672953)
          ·
            refine ⟨62820055321027634427504715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83760073761370179236672953 62820055321027634427504715)
            ·
              refine ⟨94230082981541451641257073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62820055321027634427504715 94230082981541451641257073)
              ·
                refine ⟨70672562236156088730942805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94230082981541451641257073 70672562236156088730942805)
                ·
                  refine ⟨103524261088119270601967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 70672562236156088730942805 103524261088119270601967)
                  ·
                    rfl

theorem cell23_1814515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 11].length) (baseStart_1814515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814515 prefixEnd_1814515 := by exact prefixLift 1814515
  have htrace : WordTrace (prefixWord ++ tailWord_1814515) baseStart_1814515 baseEnd_1814515 := by
    simpa [prefixWord, tailWord_1814515, baseEnd_1814515] using wordTrace_append hprefix tailTrace_1814515
  have hstable : (prefixWord ++ tailWord_1814515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814515).length < 2 ^ (prefixWord ++ tailWord_1814515).sum := by decide
  have hdescent : baseEnd_1814515 < baseStart_1814515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814599 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1814599 : Nat := 118140960795 + 1814599 * 2 ^ 59
def prefixEnd_1814599 : Nat := 4983230072969 + 3 ^ 40 * 1814599 * 2
def baseEnd_1814599 : Nat := 931761482168051106767317

theorem tailTrace_1814599 : CollatzResearch.WordTrace tailWord_1814599 prefixEnd_1814599 931761482168051106767317 := by
  unfold tailWord_1814599
  simp only [CollatzResearch.WordTrace]
  refine ⟨66183862753025206681206851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44122575168683471120804567 66183862753025206681206851)
  ·
    refine ⟨99275794129537810021810277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66183862753025206681206851 99275794129537810021810277)
    ·
      refine ⟨18614211399288339379089427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99275794129537810021810277 18614211399288339379089427)
      ·
        refine ⟨27921317098932509068634141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18614211399288339379089427 27921317098932509068634141)
        ·
          refine ⟨10470493912099690900737803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27921317098932509068634141 10470493912099690900737803)
          ·
            refine ⟨15705740868149536351106705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10470493912099690900737803 15705740868149536351106705)
            ·
              refine ⟨11779305651112152263330029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15705740868149536351106705 11779305651112152263330029)
              ·
                refine ⟨4417239619167057098748761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11779305651112152263330029 4417239619167057098748761)
                ·
                  refine ⟨3312929714375292824061571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417239619167057098748761 3312929714375292824061571)
                  ·
                    refine ⟨4969394571562939236092357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3312929714375292824061571 4969394571562939236092357)
                    ·
                      refine ⟨931761482168051106767317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4969394571562939236092357 931761482168051106767317)
                      ·
                        rfl

theorem cell23_1814599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1814599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814599 prefixEnd_1814599 := by exact prefixLift 1814599
  have htrace : WordTrace (prefixWord ++ tailWord_1814599) baseStart_1814599 baseEnd_1814599 := by
    simpa [prefixWord, tailWord_1814599, baseEnd_1814599] using wordTrace_append hprefix tailTrace_1814599
  have hstable : (prefixWord ++ tailWord_1814599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814599).length < 2 ^ (prefixWord ++ tailWord_1814599).sum := by decide
  have hdescent : baseEnd_1814599 < baseStart_1814599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814602 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1814602 : Nat := 118140960795 + 1814602 * 2 ^ 59
def prefixEnd_1814602 : Nat := 4983230072969 + 3 ^ 40 * 1814602 * 2
def baseEnd_1814602 : Nat := 931763022610014595029803

theorem tailTrace_1814602 : CollatzResearch.WordTrace tailWord_1814602 prefixEnd_1814602 931763022610014595029803 := by
  unfold tailWord_1814602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16545993043003584548391515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44122648114676225462377373 16545993043003584548391515)
  ·
    refine ⟨24818989564505376822587273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16545993043003584548391515 24818989564505376822587273)
    ·
      refine ⟨18614242173379032616940455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24818989564505376822587273 18614242173379032616940455)
      ·
        refine ⟨27921363260068548925410683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18614242173379032616940455 27921363260068548925410683)
        ·
          refine ⟨41882044890102823388116025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27921363260068548925410683 41882044890102823388116025)
          ·
            refine ⟨31411533667577117541087019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41882044890102823388116025 31411533667577117541087019)
            ·
              refine ⟨47117300501365676311630529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31411533667577117541087019 47117300501365676311630529)
              ·
                refine ⟨35337975376024257233722897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47117300501365676311630529 35337975376024257233722897)
                ·
                  refine ⟨26503481532018192925292173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35337975376024257233722897 26503481532018192925292173)
                  ·
                    refine ⟨9938805574506822346984565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26503481532018192925292173 9938805574506822346984565)
                    ·
                      refine ⟨931763022610014595029803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9938805574506822346984565 931763022610014595029803)
                      ·
                        rfl

theorem cell23_1814602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1814602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814602 prefixEnd_1814602 := by exact prefixLift 1814602
  have htrace : WordTrace (prefixWord ++ tailWord_1814602) baseStart_1814602 baseEnd_1814602 := by
    simpa [prefixWord, tailWord_1814602, baseEnd_1814602] using wordTrace_append hprefix tailTrace_1814602
  have hstable : (prefixWord ++ tailWord_1814602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814602).length < 2 ^ (prefixWord ++ tailWord_1814602).sum := by decide
  have hdescent : baseEnd_1814602 < baseStart_1814602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814639 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 6]
def baseStart_1814639 : Nat := 118140960795 + 1814639 * 2 ^ 59
def prefixEnd_1814639 : Nat := 4983230072969 + 3 ^ 40 * 1814639 * 2
def baseEnd_1814639 : Nat := 103531335710470105585237

theorem tailTrace_1814639 : CollatzResearch.WordTrace tailWord_1814639 prefixEnd_1814639 103531335710470105585237 := by
  unfold tailWord_1814639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66185321672880293512662971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44123547781920195675108647 66185321672880293512662971)
  ·
    refine ⟨99277982509320440268994457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66185321672880293512662971 99277982509320440268994457)
    ·
      refine ⟨74458486881990330201745843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99277982509320440268994457 74458486881990330201745843)
      ·
        refine ⟨111687730322985495302618765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74458486881990330201745843 111687730322985495302618765)
        ·
          refine ⟨41882898871119560738482037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111687730322985495302618765 41882898871119560738482037)
          ·
            refine ⟨3926521769167458819232691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41882898871119560738482037 3926521769167458819232691)
            ·
              refine ⟨5889782653751188228849037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926521769167458819232691 5889782653751188228849037)
              ·
                refine ⟨2208668495156695585818389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889782653751188228849037 2208668495156695585818389)
                ·
                  refine ⟨103531335710470105585237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2208668495156695585818389 103531335710470105585237)
                  ·
                    rfl

theorem cell23_1814639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 6].length) (baseStart_1814639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814639 prefixEnd_1814639 := by exact prefixLift 1814639
  have htrace : WordTrace (prefixWord ++ tailWord_1814639) baseStart_1814639 baseEnd_1814639 := by
    simpa [prefixWord, tailWord_1814639, baseEnd_1814639] using wordTrace_append hprefix tailTrace_1814639
  have hstable : (prefixWord ++ tailWord_1814639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814639).length < 2 ^ (prefixWord ++ tailWord_1814639).sum := by decide
  have hdescent : baseEnd_1814639 < baseStart_1814639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814706 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1814706 : Nat := 118140960795 + 1814706 * 2 ^ 59
def prefixEnd_1814706 : Nat := 4983230072969 + 3 ^ 40 * 1814706 * 2
def baseEnd_1814706 : Nat := 931816424598082188129325

theorem tailTrace_1814706 : CollatzResearch.WordTrace tailWord_1814706 prefixEnd_1814706 931816424598082188129325 := by
  unfold tailWord_1814706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16546941340909390988837993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44125176909091709303567981 16546941340909390988837993)
  ·
    refine ⟨12410206005682043241628495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16546941340909390988837993 12410206005682043241628495)
    ·
      refine ⟨18615309008523064862442743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12410206005682043241628495 18615309008523064862442743)
      ·
        refine ⟨27922963512784597293664115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18615309008523064862442743 27922963512784597293664115)
        ·
          refine ⟨41884445269176895940496173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27922963512784597293664115 41884445269176895940496173)
          ·
            refine ⟨15706666975941335977686065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41884445269176895940496173 15706666975941335977686065)
            ·
              refine ⟨11780000231956001983264549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15706666975941335977686065 11780000231956001983264549)
              ·
                refine ⟨2208750043491750371862103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11780000231956001983264549 2208750043491750371862103)
                ·
                  refine ⟨3313125065237625557793155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208750043491750371862103 3313125065237625557793155)
                  ·
                    refine ⟨4969687597856438336689733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3313125065237625557793155 4969687597856438336689733)
                    ·
                      refine ⟨931816424598082188129325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4969687597856438336689733 931816424598082188129325)
                      ·
                        rfl

theorem cell23_1814706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1814706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814706 prefixEnd_1814706 := by exact prefixLift 1814706
  have htrace : WordTrace (prefixWord ++ tailWord_1814706) baseStart_1814706 baseEnd_1814706 := by
    simpa [prefixWord, tailWord_1814706, baseEnd_1814706] using wordTrace_append hprefix tailTrace_1814706
  have hstable : (prefixWord ++ tailWord_1814706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814706).length < 2 ^ (prefixWord ++ tailWord_1814706).sum := by decide
  have hdescent : baseEnd_1814706 < baseStart_1814706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814769 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1814769 : Nat := 118140960795 + 1814769 * 2 ^ 59
def prefixEnd_1814769 : Nat := 4983230072969 + 3 ^ 40 * 1814769 * 2
def baseEnd_1814769 : Nat := 931848773879315441641535

theorem tailTrace_1814769 : CollatzResearch.WordTrace tailWord_1814769 prefixEnd_1814769 931848773879315441641535 := by
  unfold tailWord_1814769
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190063162409325714895361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44126708774939550476596907 66190063162409325714895361)
  ·
    refine ⟨49642547371806994286171521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66190063162409325714895361 49642547371806994286171521)
    ·
      refine ⟨37231910528855245714628641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49642547371806994286171521 37231910528855245714628641)
      ·
        refine ⟨27923932896641434285971481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37231910528855245714628641 27923932896641434285971481)
        ·
          refine ⟨20942949672481075714478611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27923932896641434285971481 20942949672481075714478611)
          ·
            refine ⟨31414424508721613571717917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20942949672481075714478611 31414424508721613571717917)
            ·
              refine ⟨11780409190770605089394219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31414424508721613571717917 11780409190770605089394219)
              ·
                refine ⟨17670613786155907634091329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11780409190770605089394219 17670613786155907634091329)
                ·
                  refine ⟨13252960339616930725568497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17670613786155907634091329 13252960339616930725568497)
                  ·
                    refine ⟨9939720254712698044176373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13252960339616930725568497 9939720254712698044176373)
                    ·
                      refine ⟨931848773879315441641535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9939720254712698044176373 931848773879315441641535)
                      ·
                        rfl

theorem cell23_1814769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1814769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814769 prefixEnd_1814769 := by exact prefixLift 1814769
  have htrace : WordTrace (prefixWord ++ tailWord_1814769) baseStart_1814769 baseEnd_1814769 := by
    simpa [prefixWord, tailWord_1814769, baseEnd_1814769] using wordTrace_append hprefix tailTrace_1814769
  have hstable : (prefixWord ++ tailWord_1814769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814769).length < 2 ^ (prefixWord ++ tailWord_1814769).sum := by decide
  have hdescent : baseEnd_1814769 < baseStart_1814769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814783 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 1, 3, 2]
def baseStart_1814783 : Nat := 118140960795 + 1814783 * 2 ^ 59
def prefixEnd_1814783 : Nat := 4983230072969 + 3 ^ 40 * 1814783 * 2
def baseEnd_1814783 : Nat := 931855962608478386866471

theorem tailTrace_1814783 : CollatzResearch.WordTrace tailWord_1814783 prefixEnd_1814783 931855962608478386866471 := by
  unfold tailWord_1814783
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190573784358606105905003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44127049189572404070603335 66190573784358606105905003)
  ·
    refine ⟨99285860676537909158857505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66190573784358606105905003 99285860676537909158857505)
    ·
      refine ⟨74464395507403431869143129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99285860676537909158857505 74464395507403431869143129)
      ·
        refine ⟨55848296630552573901857347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74464395507403431869143129 55848296630552573901857347)
        ·
          refine ⟨83772444945828860852786021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55848296630552573901857347 83772444945828860852786021)
          ·
            refine ⟨15707333427342911409897379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83772444945828860852786021 15707333427342911409897379)
            ·
              refine ⟨23561000141014367114846069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15707333427342911409897379 23561000141014367114846069)
              ·
                refine ⟨2208843763220096917016819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23561000141014367114846069 2208843763220096917016819)
                ·
                  refine ⟨3313265644830145375525229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208843763220096917016819 3313265644830145375525229)
                  ·
                    refine ⟨1242474616811304515821961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313265644830145375525229 1242474616811304515821961)
                    ·
                      refine ⟨931855962608478386866471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242474616811304515821961 931855962608478386866471)
                      ·
                        rfl

theorem cell23_1814783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_1814783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814783 prefixEnd_1814783 := by exact prefixLift 1814783
  have htrace : WordTrace (prefixWord ++ tailWord_1814783) baseStart_1814783 baseEnd_1814783 := by
    simpa [prefixWord, tailWord_1814783, baseEnd_1814783] using wordTrace_append hprefix tailTrace_1814783
  have hstable : (prefixWord ++ tailWord_1814783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814783).length < 2 ^ (prefixWord ++ tailWord_1814783).sum := by decide
  have hdescent : baseEnd_1814783 < baseStart_1814783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814789 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1814789 : Nat := 118140960795 + 1814789 * 2 ^ 59
def prefixEnd_1814789 : Nat := 4983230072969 + 3 ^ 40 * 1814789 * 2
def baseEnd_1814789 : Nat := 310619681164135121130481

theorem tailTrace_1814789 : CollatzResearch.WordTrace tailWord_1814789 prefixEnd_1814789 310619681164135121130481 := by
  unfold tailWord_1814789
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190792622336869130623421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44127195081557912753748947 66190792622336869130623421)
  ·
    refine ⟨24821547233376325923983783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66190792622336869130623421 24821547233376325923983783)
    ·
      refine ⟨37232320850064488885975675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24821547233376325923983783 37232320850064488885975675)
      ·
        refine ⟨55848481275096733328963513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37232320850064488885975675 55848481275096733328963513)
        ·
          refine ⟨41886360956322549996722635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55848481275096733328963513 41886360956322549996722635)
          ·
            refine ⟨62829541434483824995083953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41886360956322549996722635 62829541434483824995083953)
            ·
              refine ⟨47122156075862868746312965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62829541434483824995083953 47122156075862868746312965)
              ·
                refine ⟨8835404264224287889933681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47122156075862868746312965 8835404264224287889933681)
                ·
                  refine ⟨6626553198168215917450261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8835404264224287889933681 6626553198168215917450261)
                  ·
                    refine ⟨310619681164135121130481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6626553198168215917450261 310619681164135121130481)
                    ·
                      rfl

theorem cell23_1814789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1814789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814789 prefixEnd_1814789 := by exact prefixLift 1814789
  have htrace : WordTrace (prefixWord ++ tailWord_1814789) baseStart_1814789 baseEnd_1814789 := by
    simpa [prefixWord, tailWord_1814789, baseEnd_1814789] using wordTrace_append hprefix tailTrace_1814789
  have hstable : (prefixWord ++ tailWord_1814789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814789).length < 2 ^ (prefixWord ++ tailWord_1814789).sum := by decide
  have hdescent : baseEnd_1814789 < baseStart_1814789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814791 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1814791 : Nat := 118140960795 + 1814791 * 2 ^ 59
def prefixEnd_1814791 : Nat := 4983230072969 + 3 ^ 40 * 1814791 * 2
def baseEnd_1814791 : Nat := 931860070453714355566435

theorem tailTrace_1814791 : CollatzResearch.WordTrace tailWord_1814791 prefixEnd_1814791 931860070453714355566435 := by
  unfold tailWord_1814791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190865568329623472196227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44127243712219748981464151 66190865568329623472196227)
  ·
    refine ⟨99286298352494435208294341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66190865568329623472196227 99286298352494435208294341)
    ·
      refine ⟨18616180941092706601555189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99286298352494435208294341 18616180941092706601555189)
      ·
        refine ⟨1745266963227441243895799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18616180941092706601555189 1745266963227441243895799)
        ·
          refine ⟨2617900444841161865843699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745266963227441243895799 2617900444841161865843699)
          ·
            refine ⟨3926850667261742798765549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617900444841161865843699 3926850667261742798765549)
            ·
              refine ⟨1472569000223153549537081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3926850667261742798765549 1472569000223153549537081)
              ·
                refine ⟨1104426750167365162152811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472569000223153549537081 1104426750167365162152811)
                ·
                  refine ⟨1656640125251047743229217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104426750167365162152811 1656640125251047743229217)
                  ·
                    refine ⟨1242480093938285807421913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1656640125251047743229217 1242480093938285807421913)
                    ·
                      refine ⟨931860070453714355566435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242480093938285807421913 931860070453714355566435)
                      ·
                        rfl

theorem cell23_1814791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1814791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814791 prefixEnd_1814791 := by exact prefixLift 1814791
  have htrace : WordTrace (prefixWord ++ tailWord_1814791) baseStart_1814791 baseEnd_1814791 := by
    simpa [prefixWord, tailWord_1814791, baseEnd_1814791] using wordTrace_append hprefix tailTrace_1814791
  have hstable : (prefixWord ++ tailWord_1814791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814791).length < 2 ^ (prefixWord ++ tailWord_1814791).sum := by decide
  have hdescent : baseEnd_1814791 < baseStart_1814791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814807 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1814807 : Nat := 118140960795 + 1814807 * 2 ^ 59
def prefixEnd_1814807 : Nat := 4983230072969 + 3 ^ 40 * 1814807 * 2
def baseEnd_1814807 : Nat := 931868286144186292966361

theorem tailTrace_1814807 : CollatzResearch.WordTrace tailWord_1814807 prefixEnd_1814807 931868286144186292966361 := by
  unfold tailWord_1814807
  simp only [CollatzResearch.WordTrace]
  refine ⟨66191449136271658204778675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44127632757514438803185783 66191449136271658204778675)
  ·
    refine ⟨99287173704407487307168013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66191449136271658204778675 99287173704407487307168013)
    ·
      refine ⟨37232690139152807740188005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99287173704407487307168013 37232690139152807740188005)
      ·
        refine ⟨6981129401091151451285251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37232690139152807740188005 6981129401091151451285251)
        ·
          refine ⟨10471694101636727176927877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981129401091151451285251 10471694101636727176927877)
          ·
            refine ⟨1963442644056886345673977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10471694101636727176927877 1963442644056886345673977)
            ·
              refine ⟨1472581983042664759255483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963442644056886345673977 1472581983042664759255483)
              ·
                refine ⟨2208872974563997138883225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472581983042664759255483 2208872974563997138883225)
                ·
                  refine ⟨1656654730922997854162419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208872974563997138883225 1656654730922997854162419)
                  ·
                    refine ⟨2484982096384496781243629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656654730922997854162419 2484982096384496781243629)
                    ·
                      refine ⟨931868286144186292966361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2484982096384496781243629 931868286144186292966361)
                      ·
                        rfl

theorem cell23_1814807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1814807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814807 prefixEnd_1814807 := by exact prefixLift 1814807
  have htrace : WordTrace (prefixWord ++ tailWord_1814807) baseStart_1814807 baseEnd_1814807 := by
    simpa [prefixWord, tailWord_1814807, baseEnd_1814807] using wordTrace_append hprefix tailTrace_1814807
  have hstable : (prefixWord ++ tailWord_1814807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814807).length < 2 ^ (prefixWord ++ tailWord_1814807).sum := by decide
  have hdescent : baseEnd_1814807 < baseStart_1814807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814816 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1814816 : Nat := 118140960795 + 1814816 * 2 ^ 59
def prefixEnd_1814816 : Nat := 4983230072969 + 3 ^ 40 * 1814816 * 2
def baseEnd_1814816 : Nat := 931872907470076757753819

theorem tailTrace_1814816 : CollatzResearch.WordTrace tailWord_1814816 prefixEnd_1814816 931872907470076757753819 := by
  unfold tailWord_1814816
  simp only [CollatzResearch.WordTrace]
  refine ⟨33095888696619526370928151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44127851595492701827904201 33095888696619526370928151)
  ·
    refine ⟨49643833044929289556392227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33095888696619526370928151 49643833044929289556392227)
    ·
      refine ⟨74465749567393934334588341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49643833044929289556392227 74465749567393934334588341)
      ·
        refine ⟨6981164021943181343867657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74465749567393934334588341 6981164021943181343867657)
        ·
          refine ⟨5235873016457386007900743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6981164021943181343867657 5235873016457386007900743)
          ·
            refine ⟨7853809524686079011851115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235873016457386007900743 7853809524686079011851115)
            ·
              refine ⟨11780714287029118517776673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853809524686079011851115 11780714287029118517776673)
              ·
                refine ⟨8835535715271838888332505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780714287029118517776673 8835535715271838888332505)
                ·
                  refine ⟨6626651786453879166249379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8835535715271838888332505 6626651786453879166249379)
                  ·
                    refine ⟨9939977679680818749374069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626651786453879166249379 9939977679680818749374069)
                    ·
                      refine ⟨931872907470076757753819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9939977679680818749374069 931872907470076757753819)
                      ·
                        rfl

theorem cell23_1814816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1814816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814816 prefixEnd_1814816 := by exact prefixLift 1814816
  have htrace : WordTrace (prefixWord ++ tailWord_1814816) baseStart_1814816 baseEnd_1814816 := by
    simpa [prefixWord, tailWord_1814816, baseEnd_1814816] using wordTrace_append hprefix tailTrace_1814816
  have hstable : (prefixWord ++ tailWord_1814816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814816).length < 2 ^ (prefixWord ++ tailWord_1814816).sum := by decide
  have hdescent : baseEnd_1814816 < baseStart_1814816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814819 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 9]
def baseStart_1814819 : Nat := 118140960795 + 1814819 * 2 ^ 59
def prefixEnd_1814819 : Nat := 4983230072969 + 3 ^ 40 * 1814819 * 2
def baseEnd_1814819 : Nat := 103541605323560027335145

theorem tailTrace_1814819 : CollatzResearch.WordTrace tailWord_1814819 prefixEnd_1814819 103541605323560027335145 := by
  unfold tailWord_1814819
  simp only [CollatzResearch.WordTrace]
  refine ⟨66191886812228184254215511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44127924541485456169477007 66191886812228184254215511)
  ·
    refine ⟨99287830218342276381323267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66191886812228184254215511 99287830218342276381323267)
    ·
      refine ⟨148931745327513414571984901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99287830218342276381323267 148931745327513414571984901)
      ·
        refine ⟨27924702248908765232247169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148931745327513414571984901 27924702248908765232247169)
        ·
          refine ⟨20943526686681573924185377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27924702248908765232247169 20943526686681573924185377)
          ·
            refine ⟨15707645015011180443139033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20943526686681573924185377 15707645015011180443139033)
            ·
              refine ⟨11780733761258385332354275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15707645015011180443139033 11780733761258385332354275)
              ·
                refine ⟨17671100641887577998531413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11780733761258385332354275 17671100641887577998531413)
                ·
                  refine ⟨103541605323560027335145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17671100641887577998531413 103541605323560027335145)
                  ·
                    rfl

theorem cell23_1814819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 9].length) (baseStart_1814819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814819 prefixEnd_1814819 := by exact prefixLift 1814819
  have htrace : WordTrace (prefixWord ++ tailWord_1814819) baseStart_1814819 baseEnd_1814819 := by
    simpa [prefixWord, tailWord_1814819, baseEnd_1814819] using wordTrace_append hprefix tailTrace_1814819
  have hstable : (prefixWord ++ tailWord_1814819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814819).length < 2 ^ (prefixWord ++ tailWord_1814819).sum := by decide
  have hdescent : baseEnd_1814819 < baseStart_1814819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814859 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_1814859 : Nat := 118140960795 + 1814859 * 2 ^ 59
def prefixEnd_1814859 : Nat := 4983230072969 + 3 ^ 40 * 1814859 * 2
def baseEnd_1814859 : Nat := 931894987138220089516121

theorem tailTrace_1814859 : CollatzResearch.WordTrace tailWord_1814859 prefixEnd_1814859 931894987138220089516121 := by
  unfold tailWord_1814859
  simp only [CollatzResearch.WordTrace]
  refine ⟨66193345732083271085671631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44128897154722180723781087 66193345732083271085671631)
  ·
    refine ⟨99290018598124906628507447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66193345732083271085671631 99290018598124906628507447)
    ·
      refine ⟨148935027897187359942761171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99290018598124906628507447 148935027897187359942761171)
      ·
        refine ⟨223402541845781039914141757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148935027897187359942761171 223402541845781039914141757)
        ·
          refine ⟨83775953192167889967803159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223402541845781039914141757 83775953192167889967803159)
          ·
            refine ⟨125663929788251834951704739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83775953192167889967803159 125663929788251834951704739)
            ·
              refine ⟨188495894682377752427557109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125663929788251834951704739 188495894682377752427557109)
              ·
                refine ⟨17671490126472914290083479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188495894682377752427557109 17671490126472914290083479)
                ·
                  refine ⟨26507235189709371435125219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17671490126472914290083479 26507235189709371435125219)
                  ·
                    refine ⟨39760852784564057152687829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26507235189709371435125219 39760852784564057152687829)
                    ·
                      refine ⟨931894987138220089516121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39760852784564057152687829 931894987138220089516121)
                      ·
                        rfl

theorem cell23_1814859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_1814859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814859 prefixEnd_1814859 := by exact prefixLift 1814859
  have htrace : WordTrace (prefixWord ++ tailWord_1814859) baseStart_1814859 baseEnd_1814859 := by
    simpa [prefixWord, tailWord_1814859, baseEnd_1814859] using wordTrace_append hprefix tailTrace_1814859
  have hstable : (prefixWord ++ tailWord_1814859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814859).length < 2 ^ (prefixWord ++ tailWord_1814859).sum := by decide
  have hdescent : baseEnd_1814859 < baseStart_1814859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814866 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1814866 : Nat := 118140960795 + 1814866 * 2 ^ 59
def prefixEnd_1814866 : Nat := 4983230072969 + 3 ^ 40 * 1814866 * 2
def baseEnd_1814866 : Nat := 310632860500933854042863

theorem tailTrace_1814866 : CollatzResearch.WordTrace tailWord_1814866 prefixEnd_1814866 310632860500933854042863 := by
  unfold tailWord_1814866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16548400260764477820294113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44129067362038607520784301 16548400260764477820294113)
  ·
    refine ⟨12411300195573358365220585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16548400260764477820294113 12411300195573358365220585)
    ·
      refine ⟨9308475146680018773915439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12411300195573358365220585 9308475146680018773915439)
      ·
        refine ⟨13962712720020028160873159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308475146680018773915439 13962712720020028160873159)
        ·
          refine ⟨20944069080030042241309739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13962712720020028160873159 20944069080030042241309739)
          ·
            refine ⟨31416103620045063361964609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20944069080030042241309739 31416103620045063361964609)
            ·
              refine ⟨23562077715033797521473457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31416103620045063361964609 23562077715033797521473457)
              ·
                refine ⟨17671558286275348141105093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23562077715033797521473457 17671558286275348141105093)
                ·
                  refine ⟨3313417178676627776457205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17671558286275348141105093 3313417178676627776457205)
                  ·
                    refine ⟨310632860500933854042863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3313417178676627776457205 310632860500933854042863)
                    ·
                      rfl

theorem cell23_1814866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1814866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814866 prefixEnd_1814866 := by exact prefixLift 1814866
  have htrace : WordTrace (prefixWord ++ tailWord_1814866) baseStart_1814866 baseEnd_1814866 := by
    simpa [prefixWord, tailWord_1814866, baseEnd_1814866] using wordTrace_append hprefix tailTrace_1814866
  have hstable : (prefixWord ++ tailWord_1814866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814866).length < 2 ^ (prefixWord ++ tailWord_1814866).sum := by decide
  have hdescent : baseEnd_1814866 < baseStart_1814866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814906 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_1814906 : Nat := 118140960795 + 1814906 * 2 ^ 59
def prefixEnd_1814906 : Nat := 4983230072969 + 3 ^ 40 * 1814906 * 2
def baseEnd_1814906 : Nat := 931919120728981405628405

theorem tailTrace_1814906 : CollatzResearch.WordTrace tailWord_1814906 prefixEnd_1814906 931919120728981405628405 := by
  unfold tailWord_1814906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16548764990728249528158143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44130039975275332075088381 16548764990728249528158143)
  ·
    refine ⟨24823147486092374292237215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16548764990728249528158143 24823147486092374292237215)
    ·
      refine ⟨37234721229138561438355823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24823147486092374292237215 37234721229138561438355823)
      ·
        refine ⟨55852081843707842157533735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37234721229138561438355823 55852081843707842157533735)
        ·
          refine ⟨83778122765561763236300603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55852081843707842157533735 83778122765561763236300603)
          ·
            refine ⟨125667184148342644854450905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83778122765561763236300603 125667184148342644854450905)
            ·
              refine ⟨94250388111256983640838179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125667184148342644854450905 94250388111256983640838179)
              ·
                refine ⟨141375582166885475461257269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94250388111256983640838179 141375582166885475461257269)
                ·
                  refine ⟨13253960828145513324492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141375582166885475461257269 13253960828145513324492869)
                  ·
                    refine ⟨2485117655277283748342413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13253960828145513324492869 2485117655277283748342413)
                    ·
                      refine ⟨931919120728981405628405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485117655277283748342413 931919120728981405628405)
                      ·
                        rfl

theorem cell23_1814906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_1814906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814906 prefixEnd_1814906 := by exact prefixLift 1814906
  have htrace : WordTrace (prefixWord ++ tailWord_1814906) baseStart_1814906 baseEnd_1814906 := by
    simpa [prefixWord, tailWord_1814906, baseEnd_1814906] using wordTrace_append hprefix tailTrace_1814906
  have hstable : (prefixWord ++ tailWord_1814906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814906).length < 2 ^ (prefixWord ++ tailWord_1814906).sum := by decide
  have hdescent : baseEnd_1814906 < baseStart_1814906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814916 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1814916 : Nat := 118140960795 + 1814916 * 2 ^ 59
def prefixEnd_1814916 : Nat := 4983230072969 + 3 ^ 40 * 1814916 * 2
def baseEnd_1814916 : Nat := 931924255535526366503359

theorem tailTrace_1814916 : CollatzResearch.WordTrace tailWord_1814916 prefixEnd_1814916 931924255535526366503359 := by
  unfold tailWord_1814916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097712346438384910248301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44130283128584513213664401 33097712346438384910248301)
  ·
    refine ⟨12411642129914394341343113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33097712346438384910248301 12411642129914394341343113)
    ·
      refine ⟨9308731597435795756007335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12411642129914394341343113 9308731597435795756007335)
      ·
        refine ⟨13963097396153693634011003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308731597435795756007335 13963097396153693634011003)
        ·
          refine ⟨20944646094230540451016505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13963097396153693634011003 20944646094230540451016505)
          ·
            refine ⟨15708484570672905338262379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20944646094230540451016505 15708484570672905338262379)
            ·
              refine ⟨23562726856009358007393569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15708484570672905338262379 23562726856009358007393569)
              ·
                refine ⟨17672045142007018505545177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23562726856009358007393569 17672045142007018505545177)
                ·
                  refine ⟨13254033856505263879158883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17672045142007018505545177 13254033856505263879158883)
                  ·
                    refine ⟨19881050784757895818738325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13254033856505263879158883 19881050784757895818738325)
                    ·
                      refine ⟨931924255535526366503359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19881050784757895818738325 931924255535526366503359)
                      ·
                        rfl

theorem cell23_1814916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1814916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814916 prefixEnd_1814916 := by exact prefixLift 1814916
  have htrace : WordTrace (prefixWord ++ tailWord_1814916) baseStart_1814916 baseEnd_1814916 := by
    simpa [prefixWord, tailWord_1814916, baseEnd_1814916] using wordTrace_append hprefix tailTrace_1814916
  have hstable : (prefixWord ++ tailWord_1814916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814916).length < 2 ^ (prefixWord ++ tailWord_1814916).sum := by decide
  have hdescent : baseEnd_1814916 < baseStart_1814916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814947 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 1, 4]
def baseStart_1814947 : Nat := 118140960795 + 1814947 * 2 ^ 59
def prefixEnd_1814947 : Nat := 4983230072969 + 3 ^ 40 * 1814947 * 2
def baseEnd_1814947 : Nat := 310646724478605248405239

theorem tailTrace_1814947 : CollatzResearch.WordTrace tailWord_1814947 prefixEnd_1814947 310646724478605248405239 := by
  unfold tailWord_1814947
  simp only [CollatzResearch.WordTrace]
  refine ⟨66196555355764462114875095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44131036903842974743250063 66196555355764462114875095)
  ·
    refine ⟨99294833033646693172312643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66196555355764462114875095 99294833033646693172312643)
    ·
      refine ⟨148942249550470039758468965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99294833033646693172312643 148942249550470039758468965)
      ·
        refine ⟨27926671790713132454712931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148942249550470039758468965 27926671790713132454712931)
        ·
          refine ⟨41890007686069698682069397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27926671790713132454712931 41890007686069698682069397)
          ·
            refine ⟨1963594110284517125722003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41890007686069698682069397 1963594110284517125722003)
            ·
              refine ⟨2945391165426775688583005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963594110284517125722003 2945391165426775688583005)
              ·
                refine ⟨1104521687035040883218627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2945391165426775688583005 1104521687035040883218627)
                ·
                  refine ⟨1656782530552561324827941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104521687035040883218627 1656782530552561324827941)
                  ·
                    refine ⟨310646724478605248405239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1656782530552561324827941 310646724478605248405239)
                    ·
                      rfl

theorem cell23_1814947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 4].length) (baseStart_1814947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814947 prefixEnd_1814947 := by exact prefixLift 1814947
  have htrace : WordTrace (prefixWord ++ tailWord_1814947) baseStart_1814947 baseEnd_1814947 := by
    simpa [prefixWord, tailWord_1814947, baseEnd_1814947] using wordTrace_append hprefix tailTrace_1814947
  have hstable : (prefixWord ++ tailWord_1814947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814947).length < 2 ^ (prefixWord ++ tailWord_1814947).sum := by decide
  have hdescent : baseEnd_1814947 < baseStart_1814947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814953 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 3]
def baseStart_1814953 : Nat := 118140960795 + 1814953 * 2 ^ 59
def prefixEnd_1814953 : Nat := 4983230072969 + 3 ^ 40 * 1814953 * 2
def baseEnd_1814953 : Nat := 931943254319742721740689

theorem tailTrace_1814953 : CollatzResearch.WordTrace tailWord_1814953 prefixEnd_1814953 931943254319742721740689 := by
  unfold tailWord_1814953
  simp only [CollatzResearch.WordTrace]
  refine ⟨66196774193742725139593513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44131182795828483426395675 66196774193742725139593513)
  ·
    refine ⟨49647580645307043854695135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66196774193742725139593513 49647580645307043854695135)
    ·
      refine ⟨74471370967960565782042703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49647580645307043854695135 74471370967960565782042703)
      ·
        refine ⟨111707056451940848673064055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74471370967960565782042703 111707056451940848673064055)
        ·
          refine ⟨167560584677911273009596083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111707056451940848673064055 167560584677911273009596083)
          ·
            refine ⟨251340877016866909514394125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167560584677911273009596083 251340877016866909514394125)
            ·
              refine ⟨94252828881325091067897797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251340877016866909514394125 94252828881325091067897797)
              ·
                refine ⟨17672405415248454575230837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94252828881325091067897797 17672405415248454575230837)
                ·
                  refine ⟨1656788007679542616427891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17672405415248454575230837 1656788007679542616427891)
                  ·
                    refine ⟨2485182011519313924641837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656788007679542616427891 2485182011519313924641837)
                    ·
                      refine ⟨931943254319742721740689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485182011519313924641837 931943254319742721740689)
                      ·
                        rfl

theorem cell23_1814953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_1814953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814953 prefixEnd_1814953 := by exact prefixLift 1814953
  have htrace : WordTrace (prefixWord ++ tailWord_1814953) baseStart_1814953 baseEnd_1814953 := by
    simpa [prefixWord, tailWord_1814953, baseEnd_1814953] using wordTrace_append hprefix tailTrace_1814953
  have hstable : (prefixWord ++ tailWord_1814953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814953).length < 2 ^ (prefixWord ++ tailWord_1814953).sum := by decide
  have hdescent : baseEnd_1814953 < baseStart_1814953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814954 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1814954 : Nat := 118140960795 + 1814954 * 2 ^ 59
def prefixEnd_1814954 : Nat := 4983230072969 + 3 ^ 40 * 1814954 * 2
def baseEnd_1814954 : Nat := 931943767800397217828185

theorem tailTrace_1814954 : CollatzResearch.WordTrace tailWord_1814954 prefixEnd_1814954 931943767800397217828185 := by
  unfold tailWord_1814954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16549202666684775577594979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44131207111159401540253277 16549202666684775577594979)
  ·
    refine ⟨24823804000027163366392469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16549202666684775577594979 24823804000027163366392469)
    ·
      refine ⟨1163615812501273282799647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24823804000027163366392469 1163615812501273282799647)
      ·
        refine ⟨1745423718751909924199471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163615812501273282799647 1745423718751909924199471)
        ·
          refine ⟨2618135578127864886299207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745423718751909924199471 2618135578127864886299207)
          ·
            refine ⟨3927203367191797329448811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618135578127864886299207 3927203367191797329448811)
            ·
              refine ⟨5890805050787695994173217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927203367191797329448811 5890805050787695994173217)
              ·
                refine ⟨4418103788090771995629913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890805050787695994173217 4418103788090771995629913)
                ·
                  refine ⟨3313577841068078996722435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418103788090771995629913 3313577841068078996722435)
                  ·
                    refine ⟨4970366761602118495083653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3313577841068078996722435 4970366761602118495083653)
                    ·
                      refine ⟨931943767800397217828185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4970366761602118495083653 931943767800397217828185)
                      ·
                        rfl

theorem cell23_1814954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1814954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814954 prefixEnd_1814954 := by exact prefixLift 1814954
  have htrace : WordTrace (prefixWord ++ tailWord_1814954) baseStart_1814954 baseEnd_1814954 := by
    simpa [prefixWord, tailWord_1814954, baseEnd_1814954] using wordTrace_append hprefix tailTrace_1814954
  have hstable : (prefixWord ++ tailWord_1814954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814954).length < 2 ^ (prefixWord ++ tailWord_1814954).sum := by decide
  have hdescent : baseEnd_1814954 < baseStart_1814954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814956 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_1814956 : Nat := 118140960795 + 1814956 * 2 ^ 59
def prefixEnd_1814956 : Nat := 4983230072969 + 3 ^ 40 * 1814956 * 2
def baseEnd_1814956 : Nat := 310648264920568736667725

theorem tailTrace_1814956 : CollatzResearch.WordTrace tailWord_1814956 prefixEnd_1814956 310648264920568736667725 := by
  unfold tailWord_1814956
  simp only [CollatzResearch.WordTrace]
  refine ⟨33098441806365928325976361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44131255741821237767968481 33098441806365928325976361)
  ·
    refine ⟨24823831354774446244482271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33098441806365928325976361 24823831354774446244482271)
    ·
      refine ⟨37235747032161669366723407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24823831354774446244482271 37235747032161669366723407)
      ·
        refine ⟨55853620548242504050085111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37235747032161669366723407 55853620548242504050085111)
        ·
          refine ⟨83780430822363756075127667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55853620548242504050085111 83780430822363756075127667)
          ·
            refine ⟨125670646233545634112691501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83780430822363756075127667 125670646233545634112691501)
            ·
              refine ⟨47126492337579612792259313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125670646233545634112691501 47126492337579612792259313)
              ·
                refine ⟨35344869253184709594194485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47126492337579612792259313 35344869253184709594194485)
                ·
                  refine ⟨3313581492486066524455733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35344869253184709594194485 3313581492486066524455733)
                  ·
                    refine ⟨310648264920568736667725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3313581492486066524455733 310648264920568736667725)
                    ·
                      rfl

theorem cell23_1814956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_1814956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814956 prefixEnd_1814956 := by exact prefixLift 1814956
  have htrace : WordTrace (prefixWord ++ tailWord_1814956) baseStart_1814956 baseEnd_1814956 := by
    simpa [prefixWord, tailWord_1814956, baseEnd_1814956] using wordTrace_append hprefix tailTrace_1814956
  have hstable : (prefixWord ++ tailWord_1814956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814956).length < 2 ^ (prefixWord ++ tailWord_1814956).sum := by decide
  have hdescent : baseEnd_1814956 < baseStart_1814956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814957 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1814957 : Nat := 118140960795 + 1814957 * 2 ^ 59
def prefixEnd_1814957 : Nat := 4983230072969 + 3 ^ 40 * 1814957 * 2
def baseEnd_1814957 : Nat := 931945308242360706090671

theorem tailTrace_1814957 : CollatzResearch.WordTrace tailWord_1814957 prefixEnd_1814957 931945308242360706090671 := by
  unfold tailWord_1814957
  simp only [CollatzResearch.WordTrace]
  refine ⟨66196920085728233822739125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44131280057152155881826083 66196920085728233822739125)
  ·
    refine ⟨6205961258037021920881793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66196920085728233822739125 6205961258037021920881793)
    ·
      refine ⟨4654470943527766440661345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6205961258037021920881793 4654470943527766440661345)
      ·
        refine ⟨3490853207645824830496009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4654470943527766440661345 3490853207645824830496009)
        ·
          refine ⟨2618139905734368622872007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3490853207645824830496009 2618139905734368622872007)
          ·
            refine ⟨3927209858601552934308011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618139905734368622872007 3927209858601552934308011)
            ·
              refine ⟨5890814787902329401462017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927209858601552934308011 5890814787902329401462017)
              ·
                refine ⟨4418111090926747051096513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890814787902329401462017 4418111090926747051096513)
                ·
                  refine ⟨3313583318195060288322385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418111090926747051096513 3313583318195060288322385)
                  ·
                    refine ⟨2485187488646295216241789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3313583318195060288322385 2485187488646295216241789)
                    ·
                      refine ⟨931945308242360706090671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485187488646295216241789 931945308242360706090671)
                      ·
                        rfl

theorem cell23_1814957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1814957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814957 prefixEnd_1814957 := by exact prefixLift 1814957
  have htrace : WordTrace (prefixWord ++ tailWord_1814957) baseStart_1814957 baseEnd_1814957 := by
    simpa [prefixWord, tailWord_1814957, baseEnd_1814957] using wordTrace_append hprefix tailTrace_1814957
  have hstable : (prefixWord ++ tailWord_1814957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814957).length < 2 ^ (prefixWord ++ tailWord_1814957).sum := by decide
  have hdescent : baseEnd_1814957 < baseStart_1814957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814976 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1814976 : Nat := 118140960795 + 1814976 * 2 ^ 59
def prefixEnd_1814976 : Nat := 4983230072969 + 3 ^ 40 * 1814976 * 2
def baseEnd_1814976 : Nat := 931955064374796131753083

theorem tailTrace_1814976 : CollatzResearch.WordTrace tailWord_1814976 prefixEnd_1814976 931955064374796131753083 := by
  unfold tailWord_1814976
  simp only [CollatzResearch.WordTrace]
  refine ⟨33098806536329700033840391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44131742048439600045120521 33098806536329700033840391)
  ·
    refine ⟨49648209804494550050760587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33098806536329700033840391 49648209804494550050760587)
    ·
      refine ⟨74472314706741825076140881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49648209804494550050760587 74472314706741825076140881)
      ·
        refine ⟨55854236030056368807105661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74472314706741825076140881 55854236030056368807105661)
        ·
          refine ⟨20945338511271138302664623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55854236030056368807105661 20945338511271138302664623)
          ·
            refine ⟨31418007766906707453996935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20945338511271138302664623 31418007766906707453996935)
            ·
              refine ⟨47127011650360061180995403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31418007766906707453996935 47127011650360061180995403)
              ·
                refine ⟨70690517475540091771493105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47127011650360061180995403 70690517475540091771493105)
                ·
                  refine ⟨53017888106655068828619829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70690517475540091771493105 53017888106655068828619829)
                  ·
                    refine ⟨4970427009998912702683109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53017888106655068828619829 4970427009998912702683109)
                    ·
                      refine ⟨931955064374796131753083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4970427009998912702683109 931955064374796131753083)
                      ·
                        rfl

theorem cell23_1814976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1814976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814976 prefixEnd_1814976 := by exact prefixLift 1814976
  have htrace : WordTrace (prefixWord ++ tailWord_1814976) baseStart_1814976 baseEnd_1814976 := by
    simpa [prefixWord, tailWord_1814976, baseEnd_1814976] using wordTrace_append hprefix tailTrace_1814976
  have hstable : (prefixWord ++ tailWord_1814976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814976).length < 2 ^ (prefixWord ++ tailWord_1814976).sum := by decide
  have hdescent : baseEnd_1814976 < baseStart_1814976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814993 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_1814993 : Nat := 118140960795 + 1814993 * 2 ^ 59
def prefixEnd_1814993 : Nat := 4983230072969 + 3 ^ 40 * 1814993 * 2
def baseEnd_1814993 : Nat := 931963793545922565240505

theorem tailTrace_1814993 : CollatzResearch.WordTrace tailWord_1814993 prefixEnd_1814993 931963793545922565240505 := by
  unfold tailWord_1814993
  simp only [CollatzResearch.WordTrace]
  refine ⟨66198233113597811971049633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44132155409065207980699755 66198233113597811971049633)
  ·
    refine ⟨49648674835198358978287225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66198233113597811971049633 49648674835198358978287225)
    ·
      refine ⟨37236506126398769233715419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49648674835198358978287225 37236506126398769233715419)
      ·
        refine ⟨55854759189598153850573129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37236506126398769233715419 55854759189598153850573129)
        ·
          refine ⟨41891069392198615387929847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55854759189598153850573129 41891069392198615387929847)
          ·
            refine ⟨62836604088297923081894771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41891069392198615387929847 62836604088297923081894771)
            ·
              refine ⟨94254906132446884622842157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62836604088297923081894771 94254906132446884622842157)
              ·
                refine ⟨35345589799667581733565809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94254906132446884622842157 35345589799667581733565809)
                ·
                  refine ⟨26509192349750686300174357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35345589799667581733565809 26509192349750686300174357)
                  ·
                    refine ⟨1242618391394563420320673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26509192349750686300174357 1242618391394563420320673)
                    ·
                      refine ⟨931963793545922565240505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242618391394563420320673 931963793545922565240505)
                      ·
                        rfl

theorem cell23_1814993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_1814993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814993 prefixEnd_1814993 := by exact prefixLift 1814993
  have htrace : WordTrace (prefixWord ++ tailWord_1814993) baseStart_1814993 baseEnd_1814993 := by
    simpa [prefixWord, tailWord_1814993, baseEnd_1814993] using wordTrace_append hprefix tailTrace_1814993
  have hstable : (prefixWord ++ tailWord_1814993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814993).length < 2 ^ (prefixWord ++ tailWord_1814993).sum := by decide
  have hdescent : baseEnd_1814993 < baseStart_1814993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1814997 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1814997 : Nat := 118140960795 + 1814997 * 2 ^ 59
def prefixEnd_1814997 : Nat := 4983230072969 + 3 ^ 40 * 1814997 * 2
def baseEnd_1814997 : Nat := 931965847468540549590487

theorem tailTrace_1814997 : CollatzResearch.WordTrace tailWord_1814997 prefixEnd_1814997 931965847468540549590487 := by
  unfold tailWord_1814997
  simp only [CollatzResearch.WordTrace]
  refine ⟨66198379005583320654195245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44132252670388880436130163 66198379005583320654195245)
  ·
    refine ⟨24824392127093745245323217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66198379005583320654195245 24824392127093745245323217)
    ·
      refine ⟨18618294095320308933992413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24824392127093745245323217 18618294095320308933992413)
      ·
        refine ⟨6981860285745115850247155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18618294095320308933992413 6981860285745115850247155)
        ·
          refine ⟨10472790428617673775370733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981860285745115850247155 10472790428617673775370733)
          ·
            refine ⟨3927296410731627665764025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10472790428617673775370733 3927296410731627665764025)
            ·
              refine ⟨2945472308048720749323019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3927296410731627665764025 2945472308048720749323019)
              ·
                refine ⟨4418208462073081123984529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945472308048720749323019 4418208462073081123984529)
                ·
                  refine ⟨3313656346554810842988397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418208462073081123984529 3313656346554810842988397)
                  ·
                    refine ⟨1242621129958054066120649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3313656346554810842988397 1242621129958054066120649)
                    ·
                      refine ⟨931965847468540549590487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242621129958054066120649 931965847468540549590487)
                      ·
                        rfl

theorem cell23_1814997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1814997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1814997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1814997 prefixEnd_1814997 := by exact prefixLift 1814997
  have htrace : WordTrace (prefixWord ++ tailWord_1814997) baseStart_1814997 baseEnd_1814997 := by
    simpa [prefixWord, tailWord_1814997, baseEnd_1814997] using wordTrace_append hprefix tailTrace_1814997
  have hstable : (prefixWord ++ tailWord_1814997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1814997).length < 2 ^ (prefixWord ++ tailWord_1814997).sum := by decide
  have hdescent : baseEnd_1814997 < baseStart_1814997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1814997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815016 : List Nat := [2, 1, 4, 1, 1, 14]
def baseStart_1815016 : Nat := 118140960795 + 1815016 * 2 ^ 59
def prefixEnd_1815016 : Nat := 4983230072969 + 3 ^ 40 * 1815016 * 2
def baseEnd_1815016 : Nat := 3835290549798255042193

theorem tailTrace_1815016 : CollatzResearch.WordTrace tailWord_1815016 prefixEnd_1815016 3835290549798255042193 := by
  unfold tailWord_1815016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099535996257243449568451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44132714661676324599424601 33099535996257243449568451)
  ·
    refine ⟨49649303994385865174352677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33099535996257243449568451 49649303994385865174352677)
    ·
      refine ⟨9309244498947349720191127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49649303994385865174352677 9309244498947349720191127)
      ·
        refine ⟨13963866748421024580286691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309244498947349720191127 13963866748421024580286691)
        ·
          refine ⟨20945800122631536870430037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13963866748421024580286691 20945800122631536870430037)
          ·
            refine ⟨3835290549798255042193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 20945800122631536870430037 3835290549798255042193)
            ·
              rfl

theorem cell23_1815016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 14].length) (baseStart_1815016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815016 prefixEnd_1815016 := by exact prefixLift 1815016
  have htrace : WordTrace (prefixWord ++ tailWord_1815016) baseStart_1815016 baseEnd_1815016 := by
    simpa [prefixWord, tailWord_1815016, baseEnd_1815016] using wordTrace_append hprefix tailTrace_1815016
  have hstable : (prefixWord ++ tailWord_1815016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815016).length < 2 ^ (prefixWord ++ tailWord_1815016).sum := by decide
  have hdescent : baseEnd_1815016 < baseStart_1815016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815020 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_1815020 : Nat := 118140960795 + 1815020 * 2 ^ 59
def prefixEnd_1815020 : Nat := 4983230072969 + 3 ^ 40 * 1815020 * 2
def baseEnd_1815020 : Nat := 310659219174531319867627

theorem tailTrace_1815020 : CollatzResearch.WordTrace tailWord_1815020 prefixEnd_1815020 310659219174531319867627 := by
  unfold tailWord_1815020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099608942249997791141257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44132811922999997054855009 33099608942249997791141257)
  ·
    refine ⟨24824706706687498343355943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33099608942249997791141257 24824706706687498343355943)
    ·
      refine ⟨37237060060031247515033915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24824706706687498343355943 37237060060031247515033915)
      ·
        refine ⟨55855590090046871272550873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37237060060031247515033915 55855590090046871272550873)
        ·
          refine ⟨41891692567535153454413155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55855590090046871272550873 41891692567535153454413155)
          ·
            refine ⟨62837538851302730181619733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41891692567535153454413155 62837538851302730181619733)
            ·
              refine ⟨2945509633654815477263425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62837538851302730181619733 2945509633654815477263425)
              ·
                refine ⟨2209132225241111607947569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945509633654815477263425 2209132225241111607947569)
                ·
                  refine ⟨1656849168930833705960677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209132225241111607947569 1656849168930833705960677)
                  ·
                    refine ⟨310659219174531319867627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1656849168930833705960677 310659219174531319867627)
                    ·
                      rfl

theorem cell23_1815020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_1815020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815020 prefixEnd_1815020 := by exact prefixLift 1815020
  have htrace : WordTrace (prefixWord ++ tailWord_1815020) baseStart_1815020 baseEnd_1815020 := by
    simpa [prefixWord, tailWord_1815020, baseEnd_1815020] using wordTrace_append hprefix tailTrace_1815020
  have hstable : (prefixWord ++ tailWord_1815020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815020).length < 2 ^ (prefixWord ++ tailWord_1815020).sum := by decide
  have hdescent : baseEnd_1815020 < baseStart_1815020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815021 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1815021 : Nat := 118140960795 + 1815021 * 2 ^ 59
def prefixEnd_1815021 : Nat := 4983230072969 + 3 ^ 40 * 1815021 * 2
def baseEnd_1815021 : Nat := 931978171004248455690377

theorem tailTrace_1815021 : CollatzResearch.WordTrace tailWord_1815021 prefixEnd_1815021 931978171004248455690377 := by
  unfold tailWord_1815021
  simp only [CollatzResearch.WordTrace]
  refine ⟨66199254357496372753068917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44132836238330915168712611 66199254357496372753068917)
  ·
    refine ⟨6206180096015284945600211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66199254357496372753068917 6206180096015284945600211)
    ·
      refine ⟨9309270144022927418400317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206180096015284945600211 9309270144022927418400317)
      ·
        refine ⟨3490976304008597781900119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9309270144022927418400317 3490976304008597781900119)
        ·
          refine ⟨5236464456012896672850179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490976304008597781900119 5236464456012896672850179)
          ·
            refine ⟨7854696684019345009275269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236464456012896672850179 7854696684019345009275269)
            ·
              refine ⟨1472755628253627189239113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7854696684019345009275269 1472755628253627189239113)
              ·
                refine ⟨1104566721190220391929335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472755628253627189239113 1104566721190220391929335)
                ·
                  refine ⟨1656850081785330587894003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104566721190220391929335 1656850081785330587894003)
                  ·
                    refine ⟨2485275122677995881841005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656850081785330587894003 2485275122677995881841005)
                    ·
                      refine ⟨931978171004248455690377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485275122677995881841005 931978171004248455690377)
                      ·
                        rfl

theorem cell23_1815021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1815021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815021 prefixEnd_1815021 := by exact prefixLift 1815021
  have htrace : WordTrace (prefixWord ++ tailWord_1815021) baseStart_1815021 baseEnd_1815021 := by
    simpa [prefixWord, tailWord_1815021, baseEnd_1815021] using wordTrace_append hprefix tailTrace_1815021
  have hstable : (prefixWord ++ tailWord_1815021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815021).length < 2 ^ (prefixWord ++ tailWord_1815021).sum := by decide
  have hdescent : baseEnd_1815021 < baseStart_1815021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815030 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1815030 : Nat := 118140960795 + 1815030 * 2 ^ 59
def prefixEnd_1815030 : Nat := 4983230072969 + 3 ^ 40 * 1815030 * 2
def baseEnd_1815030 : Nat := 931982792330138920477835

theorem tailTrace_1815030 : CollatzResearch.WordTrace tailWord_1815030 prefixEnd_1815030 931982792330138920477835 := by
  unfold tailWord_1815030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137473913403985455634159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44133055076309178193431029 4137473913403985455634159)
  ·
    refine ⟨6206210870105978183451239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137473913403985455634159 6206210870105978183451239)
    ·
      refine ⟨9309316305158967275176859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206210870105978183451239 9309316305158967275176859)
      ·
        refine ⟨13963974457738450912765289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309316305158967275176859 13963974457738450912765289)
        ·
          refine ⟨10472980843303838184573967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13963974457738450912765289 10472980843303838184573967)
          ·
            refine ⟨15709471264955757276860951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472980843303838184573967 15709471264955757276860951)
            ·
              refine ⟨23564206897433635915291427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15709471264955757276860951 23564206897433635915291427)
              ·
                refine ⟨35346310346150453872937141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23564206897433635915291427 35346310346150453872937141)
                ·
                  refine ⟨3313716594951605050587857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35346310346150453872937141 3313716594951605050587857)
                  ·
                    refine ⟨2485287446213703787940893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3313716594951605050587857 2485287446213703787940893)
                    ·
                      refine ⟨931982792330138920477835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485287446213703787940893 931982792330138920477835)
                      ·
                        rfl

theorem cell23_1815030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1815030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815030 prefixEnd_1815030 := by exact prefixLift 1815030
  have htrace : WordTrace (prefixWord ++ tailWord_1815030) baseStart_1815030 baseEnd_1815030 := by
    simpa [prefixWord, tailWord_1815030, baseEnd_1815030] using wordTrace_append hprefix tailTrace_1815030
  have hstable : (prefixWord ++ tailWord_1815030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815030).length < 2 ^ (prefixWord ++ tailWord_1815030).sum := by decide
  have hdescent : baseEnd_1815030 < baseStart_1815030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815044 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1815044 : Nat := 118140960795 + 1815044 * 2 ^ 59
def prefixEnd_1815044 : Nat := 4983230072969 + 3 ^ 40 * 1815044 * 2
def baseEnd_1815044 : Nat := 931989981059301865702771

theorem tailTrace_1815044 : CollatzResearch.WordTrace tailWord_1815044 prefixEnd_1815044 931989981059301865702771 := by
  unfold tailWord_1815044
  simp only [CollatzResearch.WordTrace]
  refine ⟨33100046618206523840578093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44133395490942031787437457 33100046618206523840578093)
  ·
    refine ⟨12412517481827446440216785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33100046618206523840578093 12412517481827446440216785)
    ·
      refine ⟨9309388111370584830162589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12412517481827446440216785 9309388111370584830162589)
      ·
        refine ⟨3491020541763969311310971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9309388111370584830162589 3491020541763969311310971)
        ·
          refine ⟨5236530812645953966966457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491020541763969311310971 5236530812645953966966457)
          ·
            refine ⟨3927398109484465475224843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5236530812645953966966457 3927398109484465475224843)
            ·
              refine ⟨5891097164226698212837265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927398109484465475224843 5891097164226698212837265)
              ·
                refine ⟨4418322873170023659627949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891097164226698212837265 4418322873170023659627949)
                ·
                  refine ⟨1656871077438758872360481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4418322873170023659627949 1656871077438758872360481)
                  ·
                    refine ⟨1242653308079069154270361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1656871077438758872360481 1242653308079069154270361)
                    ·
                      refine ⟨931989981059301865702771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242653308079069154270361 931989981059301865702771)
                      ·
                        rfl

theorem cell23_1815044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1815044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815044 prefixEnd_1815044 := by exact prefixLift 1815044
  have htrace : WordTrace (prefixWord ++ tailWord_1815044) baseStart_1815044 baseEnd_1815044 := by
    simpa [prefixWord, tailWord_1815044, baseEnd_1815044] using wordTrace_append hprefix tailTrace_1815044
  have hstable : (prefixWord ++ tailWord_1815044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815044).length < 2 ^ (prefixWord ++ tailWord_1815044).sum := by decide
  have hdescent : baseEnd_1815044 < baseStart_1815044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815064 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_1815064 : Nat := 118140960795 + 1815064 * 2 ^ 59
def prefixEnd_1815064 : Nat := 4983230072969 + 3 ^ 40 * 1815064 * 2
def baseEnd_1815064 : Nat := 932000250672391787452679

theorem tailTrace_1815064 : CollatzResearch.WordTrace tailWord_1815064 prefixEnd_1815064 932000250672391787452679 := by
  unfold tailWord_1815064
  simp only [CollatzResearch.WordTrace]
  refine ⟨33100411348170295548442123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44133881797560394064589497 33100411348170295548442123)
  ·
    refine ⟨49650617022255443322663185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33100411348170295548442123 49650617022255443322663185)
    ·
      refine ⟨37237962766691582491997389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49650617022255443322663185 37237962766691582491997389)
      ·
        refine ⟨13964236037509343434499021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37237962766691582491997389 13964236037509343434499021)
        ·
          refine ⟨5236588514066003787937133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13964236037509343434499021 5236588514066003787937133)
          ·
            refine ⟨1963720692774751420476425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5236588514066003787937133 1963720692774751420476425)
            ·
              refine ⟨1472790519581063565357319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963720692774751420476425 1472790519581063565357319)
              ·
                refine ⟨2209185779371595348035979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472790519581063565357319 2209185779371595348035979)
                ·
                  refine ⟨3313778669057393022053969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209185779371595348035979 3313778669057393022053969)
                  ·
                    refine ⟨2485334001793044766540477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3313778669057393022053969 2485334001793044766540477)
                    ·
                      refine ⟨932000250672391787452679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485334001793044766540477 932000250672391787452679)
                      ·
                        rfl

theorem cell23_1815064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_1815064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815064 prefixEnd_1815064 := by exact prefixLift 1815064
  have htrace : WordTrace (prefixWord ++ tailWord_1815064) baseStart_1815064 baseEnd_1815064 := by
    simpa [prefixWord, tailWord_1815064, baseEnd_1815064] using wordTrace_append hprefix tailTrace_1815064
  have hstable : (prefixWord ++ tailWord_1815064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815064).length < 2 ^ (prefixWord ++ tailWord_1815064).sum := by decide
  have hdescent : baseEnd_1815064 < baseStart_1815064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815077 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_1815077 : Nat := 118140960795 + 1815077 * 2 ^ 59
def prefixEnd_1815077 : Nat := 4983230072969 + 3 ^ 40 * 1815077 * 2
def baseEnd_1815077 : Nat := 932006925920900236590119

theorem tailTrace_1815077 : CollatzResearch.WordTrace tailWord_1815077 prefixEnd_1815077 932006925920900236590119 := by
  unfold tailWord_1815077
  simp only [CollatzResearch.WordTrace]
  refine ⟨66201296845293494317107485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44134197896862329544738323 66201296845293494317107485)
  ·
    refine ⟨24825486316985060368915307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66201296845293494317107485 24825486316985060368915307)
    ·
      refine ⟨37238229475477590553372961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825486316985060368915307 37238229475477590553372961)
      ·
        refine ⟨27928672106608192915029721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37238229475477590553372961 27928672106608192915029721)
        ·
          refine ⟨20946504079956144686272291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27928672106608192915029721 20946504079956144686272291)
          ·
            refine ⟨31419756119934217029408437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20946504079956144686272291 31419756119934217029408437)
            ·
              refine ⟨2945602136243832846507041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31419756119934217029408437 2945602136243832846507041)
              ·
                refine ⟨2209201602182874634880281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945602136243832846507041 2209201602182874634880281)
                ·
                  refine ⟨1656901201637155976160211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209201602182874634880281 1656901201637155976160211)
                  ·
                    refine ⟨2485351802455733964240317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1656901201637155976160211 2485351802455733964240317)
                    ·
                      refine ⟨932006925920900236590119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485351802455733964240317 932006925920900236590119)
                      ·
                        rfl

theorem cell23_1815077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_1815077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815077 prefixEnd_1815077 := by exact prefixLift 1815077
  have htrace : WordTrace (prefixWord ++ tailWord_1815077) baseStart_1815077 baseEnd_1815077 := by
    simpa [prefixWord, tailWord_1815077, baseEnd_1815077] using wordTrace_append hprefix tailTrace_1815077
  have hstable : (prefixWord ++ tailWord_1815077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815077).length < 2 ^ (prefixWord ++ tailWord_1815077).sum := by decide
  have hdescent : baseEnd_1815077 < baseStart_1815077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815093 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1815093 : Nat := 118140960795 + 1815093 * 2 ^ 59
def prefixEnd_1815093 : Nat := 4983230072969 + 3 ^ 40 * 1815093 * 2
def baseEnd_1815093 : Nat := 310671713870457391330015

theorem tailTrace_1815093 : CollatzResearch.WordTrace tailWord_1815093 prefixEnd_1815093 310671713870457391330015 := by
  unfold tailWord_1815093
  simp only [CollatzResearch.WordTrace]
  refine ⟨66201880413235529049689933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44134586942157019366459955 66201880413235529049689933)
  ·
    refine ⟨24825705154963323393633725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66201880413235529049689933 24825705154963323393633725)
    ·
      refine ⟨9309639433111246272612647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24825705154963323393633725 9309639433111246272612647)
      ·
        refine ⟨13964459149666869408918971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309639433111246272612647 13964459149666869408918971)
        ·
          refine ⟨20946688724500304113378457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13964459149666869408918971 20946688724500304113378457)
          ·
            refine ⟨15710016543375228085033843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20946688724500304113378457 15710016543375228085033843)
            ·
              refine ⟨23565024815062842127550765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710016543375228085033843 23565024815062842127550765)
              ·
                refine ⟨8836884305648565797831537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23565024815062842127550765 8836884305648565797831537)
                ·
                  refine ⟨6627663229236424348373653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8836884305648565797831537 6627663229236424348373653)
                  ·
                    refine ⟨310671713870457391330015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6627663229236424348373653 310671713870457391330015)
                    ·
                      rfl

theorem cell23_1815093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1815093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815093 prefixEnd_1815093 := by exact prefixLift 1815093
  have htrace : WordTrace (prefixWord ++ tailWord_1815093) baseStart_1815093 baseEnd_1815093 := by
    simpa [prefixWord, tailWord_1815093, baseEnd_1815093] using wordTrace_append hprefix tailTrace_1815093
  have hstable : (prefixWord ++ tailWord_1815093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815093).length < 2 ^ (prefixWord ++ tailWord_1815093).sum := by decide
  have hdescent : baseEnd_1815093 < baseStart_1815093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815094 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1815094 : Nat := 118140960795 + 1815094 * 2 ^ 59
def prefixEnd_1815094 : Nat := 4983230072969 + 3 ^ 40 * 1815094 * 2
def baseEnd_1815094 : Nat := 932015655092026670077541

theorem tailTrace_1815094 : CollatzResearch.WordTrace tailWord_1815094 prefixEnd_1815094 932015655092026670077541 := by
  unfold tailWord_1815094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137619805389494138779771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44134611257487937480317557 4137619805389494138779771)
  ·
    refine ⟨6206429708084241208169657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137619805389494138779771 6206429708084241208169657)
    ·
      refine ⟨4654822281063180906127243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6206429708084241208169657 4654822281063180906127243)
      ·
        refine ⟨6982233421594771359190865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654822281063180906127243 6982233421594771359190865)
        ·
          refine ⟨5236675066196078519393149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6982233421594771359190865 5236675066196078519393149)
          ·
            refine ⟨1963753149823529444772431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5236675066196078519393149 1963753149823529444772431)
            ·
              refine ⟨2945629724735294167158647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963753149823529444772431 2945629724735294167158647)
              ·
                refine ⟨4418444587102941250737971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945629724735294167158647 4418444587102941250737971)
                ·
                  refine ⟨6627666880654411876106957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418444587102941250737971 6627666880654411876106957)
                  ·
                    refine ⟨2485375080245404453540109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6627666880654411876106957 2485375080245404453540109)
                    ·
                      refine ⟨932015655092026670077541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485375080245404453540109 932015655092026670077541)
                      ·
                        rfl

theorem cell23_1815094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1815094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815094 prefixEnd_1815094 := by exact prefixLift 1815094
  have htrace : WordTrace (prefixWord ++ tailWord_1815094) baseStart_1815094 baseEnd_1815094 := by
    simpa [prefixWord, tailWord_1815094, baseEnd_1815094] using wordTrace_append hprefix tailTrace_1815094
  have hstable : (prefixWord ++ tailWord_1815094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815094).length < 2 ^ (prefixWord ++ tailWord_1815094).sum := by decide
  have hdescent : baseEnd_1815094 < baseStart_1815094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815103 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1815103 : Nat := 118140960795 + 1815103 * 2 ^ 59
def prefixEnd_1815103 : Nat := 4983230072969 + 3 ^ 40 * 1815103 * 2
def baseEnd_1815103 : Nat := 932020276417917134864999

theorem tailTrace_1815103 : CollatzResearch.WordTrace tailWord_1815103 prefixEnd_1815103 932020276417917134864999 := by
  unfold tailWord_1815103
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202245143199300757553963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44134830095466200505035975 66202245143199300757553963)
  ·
    refine ⟨99303367714798951136330945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66202245143199300757553963 99303367714798951136330945)
    ·
      refine ⟨74477525786099213352248209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99303367714798951136330945 74477525786099213352248209)
      ·
        refine ⟨55858144339574410014186157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74477525786099213352248209 55858144339574410014186157)
        ·
          refine ⟨20946804127340403755319809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55858144339574410014186157 20946804127340403755319809)
          ·
            refine ⟨15710103095505302816489857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20946804127340403755319809 15710103095505302816489857)
            ·
              refine ⟨11782577321628977112367393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710103095505302816489857 11782577321628977112367393)
              ·
                refine ⟨8836932991221732834275545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11782577321628977112367393 8836932991221732834275545)
                ·
                  refine ⟨6627699743416299625706659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8836932991221732834275545 6627699743416299625706659)
                  ·
                    refine ⟨9941549615124449438559989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627699743416299625706659 9941549615124449438559989)
                    ·
                      refine ⟨932020276417917134864999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9941549615124449438559989 932020276417917134864999)
                      ·
                        rfl

theorem cell23_1815103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1815103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815103 prefixEnd_1815103 := by exact prefixLift 1815103
  have htrace : WordTrace (prefixWord ++ tailWord_1815103) baseStart_1815103 baseEnd_1815103 := by
    simpa [prefixWord, tailWord_1815103, baseEnd_1815103] using wordTrace_append hprefix tailTrace_1815103
  have hstable : (prefixWord ++ tailWord_1815103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815103).length < 2 ^ (prefixWord ++ tailWord_1815103).sum := by decide
  have hdescent : baseEnd_1815103 < baseStart_1815103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815160 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_1815160 : Nat := 118140960795 + 1815160 * 2 ^ 59
def prefixEnd_1815160 : Nat := 4983230072969 + 3 ^ 40 * 1815160 * 2
def baseEnd_1815160 : Nat := 932049544815223411852237

theorem tailTrace_1815160 : CollatzResearch.WordTrace tailWord_1815160 prefixEnd_1815160 932049544815223411852237 := by
  unfold tailWord_1815160
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102162051996399746189467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44136216069328532994919289 33102162051996399746189467)
  ·
    refine ⟨49653243077994599619284201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33102162051996399746189467 49653243077994599619284201)
    ·
      refine ⟨37239932308495949714463151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49653243077994599619284201 37239932308495949714463151)
      ·
        refine ⟨55859898462743924571694727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37239932308495949714463151 55859898462743924571694727)
        ·
          refine ⟨83789847694115886857542091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55859898462743924571694727 83789847694115886857542091)
          ·
            refine ⟨125684771541173830286313137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83789847694115886857542091 125684771541173830286313137)
            ·
              refine ⟨94263578655880372714734853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125684771541173830286313137 94263578655880372714734853)
              ·
                refine ⟨17674420997977569884012785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94263578655880372714734853 17674420997977569884012785)
                ·
                  refine ⟨13255815748483177413009589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17674420997977569884012785 13255815748483177413009589)
                  ·
                    refine ⟨1242732726420297882469649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13255815748483177413009589 1242732726420297882469649)
                    ·
                      refine ⟨932049544815223411852237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242732726420297882469649 932049544815223411852237)
                      ·
                        rfl

theorem cell23_1815160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_1815160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815160 prefixEnd_1815160 := by exact prefixLift 1815160
  have htrace : WordTrace (prefixWord ++ tailWord_1815160) baseStart_1815160 baseEnd_1815160 := by
    simpa [prefixWord, tailWord_1815160, baseEnd_1815160] using wordTrace_append hprefix tailTrace_1815160
  have hstable : (prefixWord ++ tailWord_1815160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815160).length < 2 ^ (prefixWord ++ tailWord_1815160).sum := by decide
  have hdescent : baseEnd_1815160 < baseStart_1815160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815193 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1815193 : Nat := 118140960795 + 1815193 * 2 ^ 59
def prefixEnd_1815193 : Nat := 4983230072969 + 3 ^ 40 * 1815193 * 2
def baseEnd_1815193 : Nat := 932066489676821782739585

theorem tailTrace_1815193 : CollatzResearch.WordTrace tailWord_1815193 prefixEnd_1815193 932066489676821782739585 := by
  unfold tailWord_1815193
  simp only [CollatzResearch.WordTrace]
  refine ⟨66205527712873246128330233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44137018475248830752220155 66205527712873246128330233)
  ·
    refine ⟨49654145784654934596247675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66205527712873246128330233 49654145784654934596247675)
    ·
      refine ⟨74481218676982401894371513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49654145784654934596247675 74481218676982401894371513)
      ·
        refine ⟨55860914007736801420778635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74481218676982401894371513 55860914007736801420778635)
        ·
          refine ⟨83791371011605202131167953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55860914007736801420778635 83791371011605202131167953)
          ·
            refine ⟨62843528258703901598375965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83791371011605202131167953 62843528258703901598375965)
            ·
              refine ⟨23566323097013963099390987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62843528258703901598375965 23566323097013963099390987)
              ·
                refine ⟨35349484645520944649086481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23566323097013963099390987 35349484645520944649086481)
                ·
                  refine ⟨26512113484140708486814861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35349484645520944649086481 26512113484140708486814861)
                  ·
                    refine ⟨9942042556552765682555573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26512113484140708486814861 9942042556552765682555573)
                    ·
                      refine ⟨932066489676821782739585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9942042556552765682555573 932066489676821782739585)
                      ·
                        rfl

theorem cell23_1815193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1815193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815193 prefixEnd_1815193 := by exact prefixLift 1815193
  have htrace : WordTrace (prefixWord ++ tailWord_1815193) baseStart_1815193 baseEnd_1815193 := by
    simpa [prefixWord, tailWord_1815193, baseEnd_1815193] using wordTrace_append hprefix tailTrace_1815193
  have hstable : (prefixWord ++ tailWord_1815193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815193).length < 2 ^ (prefixWord ++ tailWord_1815193).sum := by decide
  have hdescent : baseEnd_1815193 < baseStart_1815193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815203 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1815203 : Nat := 118140960795 + 1815203 * 2 ^ 59
def prefixEnd_1815203 : Nat := 4983230072969 + 3 ^ 40 * 1815203 * 2
def baseEnd_1815203 : Nat := 932071624483366743614539

theorem tailTrace_1815203 : CollatzResearch.WordTrace tailWord_1815203 prefixEnd_1815203 932071624483366743614539 := by
  unfold tailWord_1815203
  simp only [CollatzResearch.WordTrace]
  refine ⟨66205892442837017836194263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44137261628558011890796175 66205892442837017836194263)
  ·
    refine ⟨99308838664255526754291395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66205892442837017836194263 99308838664255526754291395)
    ·
      refine ⟨148963257996383290131437093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99308838664255526754291395 148963257996383290131437093)
      ·
        refine ⟨27930610874321866899644455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148963257996383290131437093 27930610874321866899644455)
        ·
          refine ⟨41895916311482800349466683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27930610874321866899644455 41895916311482800349466683)
          ·
            refine ⟨62843874467224200524200025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41895916311482800349466683 62843874467224200524200025)
            ·
              refine ⟨47132905850418150393150019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62843874467224200524200025 47132905850418150393150019)
              ·
                refine ⟨70699358775627225589725029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47132905850418150393150019 70699358775627225589725029)
                ·
                  refine ⟨13256129770430104798073443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70699358775627225589725029 13256129770430104798073443)
                  ·
                    refine ⟨19884194655645157197110165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13256129770430104798073443 19884194655645157197110165)
                    ·
                      refine ⟨932071624483366743614539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19884194655645157197110165 932071624483366743614539)
                      ·
                        rfl

theorem cell23_1815203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1815203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815203 prefixEnd_1815203 := by exact prefixLift 1815203
  have htrace : WordTrace (prefixWord ++ tailWord_1815203) baseStart_1815203 baseEnd_1815203 := by
    simpa [prefixWord, tailWord_1815203, baseEnd_1815203] using wordTrace_append hprefix tailTrace_1815203
  have hstable : (prefixWord ++ tailWord_1815203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815203).length < 2 ^ (prefixWord ++ tailWord_1815203).sum := by decide
  have hdescent : baseEnd_1815203 < baseStart_1815203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815230 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1815230 : Nat := 118140960795 + 1815230 * 2 ^ 59
def prefixEnd_1815230 : Nat := 4983230072969 + 3 ^ 40 * 1815230 * 2
def baseEnd_1815230 : Nat := 103565054273448681997435

theorem tailTrace_1815230 : CollatzResearch.WordTrace tailWord_1815230 prefixEnd_1815230 103565054273448681997435 := by
  unfold tailWord_1815230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275859651717400180928393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44137918142492800964951429 8275859651717400180928393)
  ·
    refine ⟨6206894738788050135696295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8275859651717400180928393 6206894738788050135696295)
    ·
      refine ⟨9310342108182075203544443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206894738788050135696295 9310342108182075203544443)
      ·
        refine ⟨13965513162273112805316665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310342108182075203544443 13965513162273112805316665)
        ·
          refine ⟨10474134871704834603987499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13965513162273112805316665 10474134871704834603987499)
          ·
            refine ⟨15711202307557251905981249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474134871704834603987499 15711202307557251905981249)
            ·
              refine ⟨11783401730667938929485937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15711202307557251905981249 11783401730667938929485937)
              ·
                refine ⟨8837551298000954197114453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11783401730667938929485937 8837551298000954197114453)
                ·
                  refine ⟨103565054273448681997435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8837551298000954197114453 103565054273448681997435)
                  ·
                    rfl

theorem cell23_1815230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1815230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815230 prefixEnd_1815230 := by exact prefixLift 1815230
  have htrace : WordTrace (prefixWord ++ tailWord_1815230) baseStart_1815230 baseEnd_1815230 := by
    simpa [prefixWord, tailWord_1815230, baseEnd_1815230] using wordTrace_append hprefix tailTrace_1815230
  have hstable : (prefixWord ++ tailWord_1815230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815230).length < 2 ^ (prefixWord ++ tailWord_1815230).sum := by decide
  have hdescent : baseEnd_1815230 < baseStart_1815230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815290 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_1815290 : Nat := 118140960795 + 1815290 * 2 ^ 59
def prefixEnd_1815290 : Nat := 4983230072969 + 3 ^ 40 * 1815290 * 2
def baseEnd_1815290 : Nat := 310705432433435967742213

theorem tailTrace_1815290 : CollatzResearch.WordTrace tailWord_1815290 prefixEnd_1815290 310705432433435967742213 := by
  unfold tailWord_1815290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552266398380457923652831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44139377062347887796407549 16552266398380457923652831)
  ·
    refine ⟨24828399597570686885479247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16552266398380457923652831 24828399597570686885479247)
    ·
      refine ⟨37242599396356030328218871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24828399597570686885479247 37242599396356030328218871)
      ·
        refine ⟨55863899094534045492328307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37242599396356030328218871 55863899094534045492328307)
        ·
          refine ⟨83795848641801068238492461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55863899094534045492328307 83795848641801068238492461)
          ·
            refine ⟨31423443240675400589434673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83795848641801068238492461 31423443240675400589434673)
            ·
              refine ⟨23567582430506550442076005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31423443240675400589434673 23567582430506550442076005)
              ·
                refine ⟨4418921705719978207889251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23567582430506550442076005 4418921705719978207889251)
                ·
                  refine ⟨6628382558579967311833877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418921705719978207889251 6628382558579967311833877)
                  ·
                    refine ⟨310705432433435967742213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6628382558579967311833877 310705432433435967742213)
                    ·
                      rfl

theorem cell23_1815290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_1815290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815290 prefixEnd_1815290 := by exact prefixLift 1815290
  have htrace : WordTrace (prefixWord ++ tailWord_1815290) baseStart_1815290 baseEnd_1815290 := by
    simpa [prefixWord, tailWord_1815290, baseEnd_1815290] using wordTrace_append hprefix tailTrace_1815290
  have hstable : (prefixWord ++ tailWord_1815290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815290).length < 2 ^ (prefixWord ++ tailWord_1815290).sum := by decide
  have hdescent : baseEnd_1815290 < baseStart_1815290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815294 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1815294 : Nat := 118140960795 + 1815294 * 2 ^ 59
def prefixEnd_1815294 : Nat := 4983230072969 + 3 ^ 40 * 1815294 * 2
def baseEnd_1815294 : Nat := 310706117074308629192207

theorem tailTrace_1815294 : CollatzResearch.WordTrace tailWord_1815294 prefixEnd_1815294 310706117074308629192207 := by
  unfold tailWord_1815294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276151435688417547219617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44139474323671560251837957 8276151435688417547219617)
  ·
    refine ⟨6207113576766313160414713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8276151435688417547219617 6207113576766313160414713)
    ·
      refine ⟨4655335182574734870311035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6207113576766313160414713 4655335182574734870311035)
      ·
        refine ⟨6983002773862102305466553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655335182574734870311035 6983002773862102305466553)
        ·
          refine ⟨5237252080396576729099915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983002773862102305466553 5237252080396576729099915)
          ·
            refine ⟨7855878120594865093649873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237252080396576729099915 7855878120594865093649873)
            ·
              refine ⟨5891908590446148820237405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7855878120594865093649873 5891908590446148820237405)
              ·
                refine ⟨2209465721417305807589027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5891908590446148820237405 2209465721417305807589027)
                ·
                  refine ⟨3314198582125958711383541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209465721417305807589027 3314198582125958711383541)
                  ·
                    refine ⟨310706117074308629192207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3314198582125958711383541 310706117074308629192207)
                    ·
                      rfl

theorem cell23_1815294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1815294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815294 prefixEnd_1815294 := by exact prefixLift 1815294
  have htrace : WordTrace (prefixWord ++ tailWord_1815294) baseStart_1815294 baseEnd_1815294 := by
    simpa [prefixWord, tailWord_1815294, baseEnd_1815294] using wordTrace_append hprefix tailTrace_1815294
  have hstable : (prefixWord ++ tailWord_1815294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815294).length < 2 ^ (prefixWord ++ tailWord_1815294).sum := by decide
  have hdescent : baseEnd_1815294 < baseStart_1815294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815307 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 2, 4]
def baseStart_1815307 : Nat := 118140960795 + 1815307 * 2 ^ 59
def prefixEnd_1815307 : Nat := 4983230072969 + 3 ^ 40 * 1815307 * 2
def baseEnd_1815307 : Nat := 310708342157144778904687

theorem tailTrace_1815307 : CollatzResearch.WordTrace tailWord_1815307 prefixEnd_1815307 310708342157144778904687 := by
  unfold tailWord_1815307
  simp only [CollatzResearch.WordTrace]
  refine ⟨66209685634460243597980175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44139790422973495731986783 66209685634460243597980175)
  ·
    refine ⟨99314528451690365396970263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66209685634460243597980175 99314528451690365396970263)
    ·
      refine ⟨148971792677535548095455395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99314528451690365396970263 148971792677535548095455395)
      ·
        refine ⟨223457689016303322143183093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148971792677535548095455395 223457689016303322143183093)
        ·
          refine ⟨20949158345278436450923415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223457689016303322143183093 20949158345278436450923415)
          ·
            refine ⟨31423737517917654676385123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20949158345278436450923415 31423737517917654676385123)
            ·
              refine ⟨47135606276876482014577685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31423737517917654676385123 47135606276876482014577685)
              ·
                refine ⟨2209481544228585094433329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47135606276876482014577685 2209481544228585094433329)
                ·
                  refine ⟨1657111158171438820824997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209481544228585094433329 1657111158171438820824997)
                  ·
                    refine ⟨310708342157144778904687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657111158171438820824997 310708342157144778904687)
                    ·
                      rfl

theorem cell23_1815307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 4].length) (baseStart_1815307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815307 prefixEnd_1815307 := by exact prefixLift 1815307
  have htrace : WordTrace (prefixWord ++ tailWord_1815307) baseStart_1815307 baseEnd_1815307 := by
    simpa [prefixWord, tailWord_1815307, baseEnd_1815307] using wordTrace_append hprefix tailTrace_1815307
  have hstable : (prefixWord ++ tailWord_1815307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815307).length < 2 ^ (prefixWord ++ tailWord_1815307).sum := by decide
  have hdescent : baseEnd_1815307 < baseStart_1815307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815317 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_1815317 : Nat := 118140960795 + 1815317 * 2 ^ 59
def prefixEnd_1815317 : Nat := 4983230072969 + 3 ^ 40 * 1815317 * 2
def baseEnd_1815317 : Nat := 932130161277979297589015

theorem tailTrace_1815317 : CollatzResearch.WordTrace tailWord_1815317 prefixEnd_1815317 932130161277979297589015 := by
  unfold tailWord_1815317
  simp only [CollatzResearch.WordTrace]
  refine ⟨66210050364424015305844205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44140033576282676870562803 66210050364424015305844205)
  ·
    refine ⟨24828768886659005739691577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66210050364424015305844205 24828768886659005739691577)
    ·
      refine ⟨18621576664994254304768683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24828768886659005739691577 18621576664994254304768683)
      ·
        refine ⟨27932364997491381457153025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18621576664994254304768683 27932364997491381457153025)
        ·
          refine ⟨20949273748118536092864769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27932364997491381457153025 20949273748118536092864769)
          ·
            refine ⟨15711955311088902069648577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20949273748118536092864769 15711955311088902069648577)
            ·
              refine ⟨11783966483316676552236433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15711955311088902069648577 11783966483316676552236433)
              ·
                refine ⟨8837974862487507414177325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11783966483316676552236433 8837974862487507414177325)
                ·
                  refine ⟨3314240573432815280316497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8837974862487507414177325 3314240573432815280316497)
                  ·
                    refine ⟨2485680430074611460237373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3314240573432815280316497 2485680430074611460237373)
                    ·
                      refine ⟨932130161277979297589015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485680430074611460237373 932130161277979297589015)
                      ·
                        rfl

theorem cell23_1815317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_1815317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815317 prefixEnd_1815317 := by exact prefixLift 1815317
  have htrace : WordTrace (prefixWord ++ tailWord_1815317) baseStart_1815317 baseEnd_1815317 := by
    simpa [prefixWord, tailWord_1815317, baseEnd_1815317] using wordTrace_append hprefix tailTrace_1815317
  have hstable : (prefixWord ++ tailWord_1815317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815317).length < 2 ^ (prefixWord ++ tailWord_1815317).sum := by decide
  have hdescent : baseEnd_1815317 < baseStart_1815317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815324 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1815324 : Nat := 118140960795 + 1815324 * 2 ^ 59
def prefixEnd_1815324 : Nat := 4983230072969 + 3 ^ 40 * 1815324 * 2
def baseEnd_1815324 : Nat := 310711251880853590067161

theorem tailTrace_1815324 : CollatzResearch.WordTrace tailWord_1815324 prefixEnd_1815324 310711251880853590067161 := by
  unfold tailWord_1815324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105152837699327750674513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44140203783599103667566017 33105152837699327750674513)
  ·
    refine ⟨24828864628274495813005885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33105152837699327750674513 24828864628274495813005885)
    ·
      refine ⟨9310824235602935929877207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24828864628274495813005885 9310824235602935929877207)
      ·
        refine ⟨13966236353404403894815811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310824235602935929877207 13966236353404403894815811)
        ·
          refine ⟨20949354530106605842223717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966236353404403894815811 20949354530106605842223717)
          ·
            refine ⟨3928003974394988595416947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20949354530106605842223717 3928003974394988595416947)
            ·
              refine ⟨5892005961592482893125421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928003974394988595416947 5892005961592482893125421)
              ·
                refine ⟨2209502235597181084922033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5892005961592482893125421 2209502235597181084922033)
                ·
                  refine ⟨1657126676697885813691525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209502235597181084922033 1657126676697885813691525)
                  ·
                    refine ⟨310711251880853590067161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657126676697885813691525 310711251880853590067161)
                    ·
                      rfl

theorem cell23_1815324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1815324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815324 prefixEnd_1815324 := by exact prefixLift 1815324
  have htrace : WordTrace (prefixWord ++ tailWord_1815324) baseStart_1815324 baseEnd_1815324 := by
    simpa [prefixWord, tailWord_1815324, baseEnd_1815324] using wordTrace_append hprefix tailTrace_1815324
  have hstable : (prefixWord ++ tailWord_1815324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815324).length < 2 ^ (prefixWord ++ tailWord_1815324).sum := by decide
  have hdescent : baseEnd_1815324 < baseStart_1815324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815341 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1815341 : Nat := 118140960795 + 1815341 * 2 ^ 59
def prefixEnd_1815341 : Nat := 4983230072969 + 3 ^ 40 * 1815341 * 2
def baseEnd_1815341 : Nat := 310714161604562401229635

theorem tailTrace_1815341 : CollatzResearch.WordTrace tailWord_1815341 prefixEnd_1815341 310714161604562401229635 := by
  unfold tailWord_1815341
  simp only [CollatzResearch.WordTrace]
  refine ⟨66210925716337067404717877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44140617144224711603145251 66210925716337067404717877)
  ·
    refine ⟨6207274285906600069192301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66210925716337067404717877 6207274285906600069192301)
    ·
      refine ⟨2327727857214975025947113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6207274285906600069192301 2327727857214975025947113)
      ·
        refine ⟨1745795892911231269460335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327727857214975025947113 1745795892911231269460335)
        ·
          refine ⟨2618693839366846904190503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745795892911231269460335 2618693839366846904190503)
          ·
            refine ⟨3928040759050270356285755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618693839366846904190503 3928040759050270356285755)
            ·
              refine ⟨5892061138575405534428633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928040759050270356285755 5892061138575405534428633)
              ·
                refine ⟨4419045853931554150821475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5892061138575405534428633 4419045853931554150821475)
                ·
                  refine ⟨6628568780897331226232213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419045853931554150821475 6628568780897331226232213)
                  ·
                    refine ⟨310714161604562401229635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6628568780897331226232213 310714161604562401229635)
                    ·
                      rfl

theorem cell23_1815341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1815341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815341 prefixEnd_1815341 := by exact prefixLift 1815341
  have htrace : WordTrace (prefixWord ++ tailWord_1815341) baseStart_1815341 baseEnd_1815341 := by
    simpa [prefixWord, tailWord_1815341, baseEnd_1815341] using wordTrace_append hprefix tailTrace_1815341
  have hstable : (prefixWord ++ tailWord_1815341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815341).length < 2 ^ (prefixWord ++ tailWord_1815341).sum := by decide
  have hdescent : baseEnd_1815341 < baseStart_1815341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815347 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3]
def baseStart_1815347 : Nat := 118140960795 + 1815347 * 2 ^ 59
def prefixEnd_1815347 : Nat := 4983230072969 + 3 ^ 40 * 1815347 * 2
def baseEnd_1815347 : Nat := 932145565697614180213877

theorem tailTrace_1815347 : CollatzResearch.WordTrace tailWord_1815347 prefixEnd_1815347 932145565697614180213877 := by
  unfold tailWord_1815347
  simp only [CollatzResearch.WordTrace]
  refine ⟨66211144554315330429436295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44140763036210220286290863 66211144554315330429436295)
  ·
    refine ⟨99316716831472995644154443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66211144554315330429436295 99316716831472995644154443)
    ·
      refine ⟨148975075247209493466231665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99316716831472995644154443 148975075247209493466231665)
      ·
        refine ⟨111731306435407120099673749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148975075247209493466231665 111731306435407120099673749)
        ·
          refine ⟨5237404989159708754672207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111731306435407120099673749 5237404989159708754672207)
          ·
            refine ⟨7856107483739563132008311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237404989159708754672207 7856107483739563132008311)
            ·
              refine ⟨11784161225609344698012467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856107483739563132008311 11784161225609344698012467)
              ·
                refine ⟨17676241838414017047018701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784161225609344698012467 17676241838414017047018701)
                ·
                  refine ⟨6628590689405256392632013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17676241838414017047018701 6628590689405256392632013)
                  ·
                    refine ⟨2485721508526971147237005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6628590689405256392632013 2485721508526971147237005)
                    ·
                      refine ⟨932145565697614180213877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2485721508526971147237005 932145565697614180213877)
                      ·
                        rfl

theorem cell23_1815347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_1815347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815347 prefixEnd_1815347 := by exact prefixLift 1815347
  have htrace : WordTrace (prefixWord ++ tailWord_1815347) baseStart_1815347 baseEnd_1815347 := by
    simpa [prefixWord, tailWord_1815347, baseEnd_1815347] using wordTrace_append hprefix tailTrace_1815347
  have hstable : (prefixWord ++ tailWord_1815347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815347).length < 2 ^ (prefixWord ++ tailWord_1815347).sum := by decide
  have hdescent : baseEnd_1815347 < baseStart_1815347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815348 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_1815348 : Nat := 118140960795 + 1815348 * 2 ^ 59
def prefixEnd_1815348 : Nat := 4983230072969 + 3 ^ 40 * 1815348 * 2
def baseEnd_1815348 : Nat := 932146079178268676301373

theorem tailTrace_1815348 : CollatzResearch.WordTrace tailWord_1815348 prefixEnd_1815348 932146079178268676301373 := by
  unfold tailWord_1815348
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105590513655853800111349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44140787351541138400148465 33105590513655853800111349)
  ·
    refine ⟨3103649110655236293760439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33105590513655853800111349 3103649110655236293760439)
    ·
      refine ⟨4655473665982854440640659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103649110655236293760439 4655473665982854440640659)
      ·
        refine ⟨6983210498974281660960989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655473665982854440640659 6983210498974281660960989)
        ·
          refine ⟨2618703937115355622860371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6983210498974281660960989 2618703937115355622860371)
          ·
            refine ⟨3928055905673033434290557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618703937115355622860371 3928055905673033434290557)
            ·
              refine ⟨1473020964627387537858959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3928055905673033434290557 1473020964627387537858959)
              ·
                refine ⟨2209531446941081306788439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473020964627387537858959 2209531446941081306788439)
                ·
                  refine ⟨3314297170411621960182659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209531446941081306788439 3314297170411621960182659)
                  ·
                    refine ⟨4971445755617432940273989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3314297170411621960182659 4971445755617432940273989)
                    ·
                      refine ⟨932146079178268676301373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4971445755617432940273989 932146079178268676301373)
                      ·
                        rfl

theorem cell23_1815348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_1815348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815348 prefixEnd_1815348 := by exact prefixLift 1815348
  have htrace : WordTrace (prefixWord ++ tailWord_1815348) baseStart_1815348 baseEnd_1815348 := by
    simpa [prefixWord, tailWord_1815348, baseEnd_1815348] using wordTrace_append hprefix tailTrace_1815348
  have hstable : (prefixWord ++ tailWord_1815348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815348).length < 2 ^ (prefixWord ++ tailWord_1815348).sum := by decide
  have hdescent : baseEnd_1815348 < baseStart_1815348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815360 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1815360 : Nat := 118140960795 + 1815360 * 2 ^ 59
def prefixEnd_1815360 : Nat := 4983230072969 + 3 ^ 40 * 1815360 * 2
def baseEnd_1815360 : Nat := 932152240946122629351317

theorem tailTrace_1815360 : CollatzResearch.WordTrace tailWord_1815360 prefixEnd_1815360 932152240946122629351317 := by
  unfold tailWord_1815360
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105809351634116824829767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44141079135512155766439689 33105809351634116824829767)
  ·
    refine ⟨49658714027451175237244651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33105809351634116824829767 49658714027451175237244651)
    ·
      refine ⟨74488071041176762855866977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49658714027451175237244651 74488071041176762855866977)
      ·
        refine ⟨55866053280882572141900233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74488071041176762855866977 55866053280882572141900233)
        ·
          refine ⟨41899539960661929106425175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55866053280882572141900233 41899539960661929106425175)
          ·
            refine ⟨62849309940992893659637763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41899539960661929106425175 62849309940992893659637763)
            ·
              refine ⟨94273964911489340489456645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62849309940992893659637763 94273964911489340489456645)
              ·
                refine ⟨17676368420904251341773121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94273964911489340489456645 17676368420904251341773121)
                ·
                  refine ⟨13257276315678188506329841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17676368420904251341773121 13257276315678188506329841)
                  ·
                    refine ⟨9942957236758641379747381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13257276315678188506329841 9942957236758641379747381)
                    ·
                      refine ⟨932152240946122629351317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9942957236758641379747381 932152240946122629351317)
                      ·
                        rfl

theorem cell23_1815360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1815360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815360 prefixEnd_1815360 := by exact prefixLift 1815360
  have htrace : WordTrace (prefixWord ++ tailWord_1815360) baseStart_1815360 baseEnd_1815360 := by
    simpa [prefixWord, tailWord_1815360, baseEnd_1815360] using wordTrace_append hprefix tailTrace_1815360
  have hstable : (prefixWord ++ tailWord_1815360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815360).length < 2 ^ (prefixWord ++ tailWord_1815360).sum := by decide
  have hdescent : baseEnd_1815360 < baseStart_1815360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815404 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_1815404 : Nat := 118140960795 + 1815404 * 2 ^ 59
def prefixEnd_1815404 : Nat := 4983230072969 + 3 ^ 40 * 1815404 * 2
def baseEnd_1815404 : Nat := 932174834094920457201115

theorem tailTrace_1815404 : CollatzResearch.WordTrace tailWord_1815404 prefixEnd_1815404 932174834094920457201115 := by
  unfold tailWord_1815404
  simp only [CollatzResearch.WordTrace]
  refine ⟨33106611757554414582130633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44142149010072552776174177 33106611757554414582130633)
  ·
    refine ⟨24829958818165810936597975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33106611757554414582130633 24829958818165810936597975)
    ·
      refine ⟨37244938227248716404896963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24829958818165810936597975 37244938227248716404896963)
      ·
        refine ⟨55867407340873074607345445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37244938227248716404896963 55867407340873074607345445)
        ·
          refine ⟨10475138876413701488877271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55867407340873074607345445 10475138876413701488877271)
          ·
            refine ⟨15712708314620552233315907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10475138876413701488877271 15712708314620552233315907)
            ·
              refine ⟨23569062471930828349973861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15712708314620552233315907 23569062471930828349973861)
              ·
                refine ⟨4419199213487030315620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23569062471930828349973861 4419199213487030315620099)
                ·
                  refine ⟨6628798820230545473430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419199213487030315620099 6628798820230545473430149)
                  ·
                    refine ⟨1242899778793227276268153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6628798820230545473430149 1242899778793227276268153)
                    ·
                      refine ⟨932174834094920457201115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1242899778793227276268153 932174834094920457201115)
                      ·
                        rfl

theorem cell23_1815404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_1815404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815404 prefixEnd_1815404 := by exact prefixLift 1815404
  have htrace : WordTrace (prefixWord ++ tailWord_1815404) baseStart_1815404 baseEnd_1815404 := by
    simpa [prefixWord, tailWord_1815404, baseEnd_1815404] using wordTrace_append hprefix tailTrace_1815404
  have hstable : (prefixWord ++ tailWord_1815404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815404).length < 2 ^ (prefixWord ++ tailWord_1815404).sum := by decide
  have hdescent : baseEnd_1815404 < baseStart_1815404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815414 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1815414 : Nat := 118140960795 + 1815414 * 2 ^ 59
def prefixEnd_1815414 : Nat := 4983230072969 + 3 ^ 40 * 1815414 * 2
def baseEnd_1815414 : Nat := 310726656300488472692023

theorem tailTrace_1815414 : CollatzResearch.WordTrace tailWord_1815414 prefixEnd_1815414 310726656300488472692023 := by
  unfold tailWord_1815414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138349265317037554507831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44142392163381733914750197 4138349265317037554507831)
  ·
    refine ⟨6207523897975556331761747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138349265317037554507831 6207523897975556331761747)
    ·
      refine ⟨9311285846963334497642621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207523897975556331761747 9311285846963334497642621)
      ·
        refine ⟨3491732192611250436615983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9311285846963334497642621 3491732192611250436615983)
        ·
          refine ⟨5237598288916875654923975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491732192611250436615983 5237598288916875654923975)
          ·
            refine ⟨7856397433375313482385963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237598288916875654923975 7856397433375313482385963)
            ·
              refine ⟨11784596150062970223578945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856397433375313482385963 11784596150062970223578945)
              ·
                refine ⟨8838447112547227667684209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11784596150062970223578945 8838447112547227667684209)
                ·
                  refine ⟨6628835334410420750763157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838447112547227667684209 6628835334410420750763157)
                  ·
                    refine ⟨310726656300488472692023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6628835334410420750763157 310726656300488472692023)
                    ·
                      rfl

theorem cell23_1815414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1815414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815414 prefixEnd_1815414 := by exact prefixLift 1815414
  have htrace : WordTrace (prefixWord ++ tailWord_1815414) baseStart_1815414 baseEnd_1815414 := by
    simpa [prefixWord, tailWord_1815414, baseEnd_1815414] using wordTrace_append hprefix tailTrace_1815414
  have hstable : (prefixWord ++ tailWord_1815414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815414).length < 2 ^ (prefixWord ++ tailWord_1815414).sum := by decide
  have hdescent : baseEnd_1815414 < baseStart_1815414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815417 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1815417 : Nat := 118140960795 + 1815417 * 2 ^ 59
def prefixEnd_1815417 : Nat := 4983230072969 + 3 ^ 40 * 1815417 * 2
def baseEnd_1815417 : Nat := 932181509343428906338555

theorem tailTrace_1815417 : CollatzResearch.WordTrace tailWord_1815417 prefixEnd_1815417 932181509343428906338555 := by
  unfold tailWord_1815417
  simp only [CollatzResearch.WordTrace]
  refine ⟨66213697664061732384484505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44142465109374488256323003 66213697664061732384484505)
  ·
    refine ⟨49660273248046299288363379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66213697664061732384484505 49660273248046299288363379)
    ·
      refine ⟨74490409872069448932545069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49660273248046299288363379 74490409872069448932545069)
      ·
        refine ⟨27933903702026043349704401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74490409872069448932545069 27933903702026043349704401)
        ·
          refine ⟨20950427776519532512278301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27933903702026043349704401 20950427776519532512278301)
          ·
            refine ⟨7856410416194824692104363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20950427776519532512278301 7856410416194824692104363)
            ·
              refine ⟨11784615624292237038156545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856410416194824692104363 11784615624292237038156545)
              ·
                refine ⟨8838461718219177778617409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11784615624292237038156545 8838461718219177778617409)
                ·
                  refine ⟨6628846288664383333963057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838461718219177778617409 6628846288664383333963057)
                  ·
                    refine ⟨4971634716498287500472293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628846288664383333963057 4971634716498287500472293)
                    ·
                      refine ⟨932181509343428906338555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4971634716498287500472293 932181509343428906338555)
                      ·
                        rfl

theorem cell23_1815417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1815417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815417 prefixEnd_1815417 := by exact prefixLift 1815417
  have htrace : WordTrace (prefixWord ++ tailWord_1815417) baseStart_1815417 baseEnd_1815417 := by
    simpa [prefixWord, tailWord_1815417, baseEnd_1815417] using wordTrace_append hprefix tailTrace_1815417
  have hstable : (prefixWord ++ tailWord_1815417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815417).length < 2 ^ (prefixWord ++ tailWord_1815417).sum := by decide
  have hdescent : baseEnd_1815417 < baseStart_1815417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815427 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 7]
def baseStart_1815427 : Nat := 118140960795 + 1815427 * 2 ^ 59
def prefixEnd_1815427 : Nat := 4983230072969 + 3 ^ 40 * 1815427 * 2
def baseEnd_1815427 : Nat := 103576293794441540801501

theorem tailTrace_1815427 : CollatzResearch.WordTrace tailWord_1815427 prefixEnd_1815427 103576293794441540801501 := by
  unfold tailWord_1815427
  simp only [CollatzResearch.WordTrace]
  refine ⟨66214062394025504092348535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44142708262683669394899023 66214062394025504092348535)
  ·
    refine ⟨99321093591038256138522803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66214062394025504092348535 99321093591038256138522803)
    ·
      refine ⟨148981640386557384207784205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99321093591038256138522803 148981640386557384207784205)
      ·
        refine ⟨55868115144959019077919077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148981640386557384207784205 55868115144959019077919077)
        ·
          refine ⟨10475271589679816077109827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55868115144959019077919077 10475271589679816077109827)
          ·
            refine ⟨15712907384519724115664741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10475271589679816077109827 15712907384519724115664741)
            ·
              refine ⟨2946170134597448271687139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15712907384519724115664741 2946170134597448271687139)
              ·
                refine ⟨4419255201896172407530709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946170134597448271687139 4419255201896172407530709)
                ·
                  refine ⟨103576293794441540801501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4419255201896172407530709 103576293794441540801501)
                  ·
                    rfl

theorem cell23_1815427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 7].length) (baseStart_1815427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815427 prefixEnd_1815427 := by exact prefixLift 1815427
  have htrace : WordTrace (prefixWord ++ tailWord_1815427) baseStart_1815427 baseEnd_1815427 := by
    simpa [prefixWord, tailWord_1815427, baseEnd_1815427] using wordTrace_append hprefix tailTrace_1815427
  have hstable : (prefixWord ++ tailWord_1815427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815427).length < 2 ^ (prefixWord ++ tailWord_1815427).sum := by decide
  have hdescent : baseEnd_1815427 < baseStart_1815427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815434 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1815434 : Nat := 118140960795 + 1815434 * 2 ^ 59
def prefixEnd_1815434 : Nat := 4983230072969 + 3 ^ 40 * 1815434 * 2
def baseEnd_1815434 : Nat := 932190238514555339825977

theorem tailTrace_1815434 : CollatzResearch.WordTrace tailWord_1815434 prefixEnd_1815434 932190238514555339825977 := by
  unfold tailWord_1815434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553579426250036071963339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44142878470000096191902237 16553579426250036071963339)
  ·
    refine ⟨24830369139375054107945009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16553579426250036071963339 24830369139375054107945009)
    ·
      refine ⟨18622776854531290580958757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24830369139375054107945009 18622776854531290580958757)
      ·
        refine ⟨3491770660224616983929767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18622776854531290580958757 3491770660224616983929767)
        ·
          refine ⟨5237655990336925475894651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491770660224616983929767 5237655990336925475894651)
          ·
            refine ⟨7856483985505388213841977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237655990336925475894651 7856483985505388213841977)
            ·
              refine ⟨5892362989129041160381483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7856483985505388213841977 5892362989129041160381483)
              ·
                refine ⟨8838544483693561740572225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892362989129041160381483 8838544483693561740572225)
                ·
                  refine ⟨6628908362770171305429169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838544483693561740572225 6628908362770171305429169)
                  ·
                    refine ⟨4971681272077628479071877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628908362770171305429169 4971681272077628479071877)
                    ·
                      refine ⟨932190238514555339825977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4971681272077628479071877 932190238514555339825977)
                      ·
                        rfl

theorem cell23_1815434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1815434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815434 prefixEnd_1815434 := by exact prefixLift 1815434
  have htrace : WordTrace (prefixWord ++ tailWord_1815434) baseStart_1815434 baseEnd_1815434 := by
    simpa [prefixWord, tailWord_1815434, baseEnd_1815434] using wordTrace_append hprefix tailTrace_1815434
  have hstable : (prefixWord ++ tailWord_1815434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815434).length < 2 ^ (prefixWord ++ tailWord_1815434).sum := by decide
  have hdescent : baseEnd_1815434 < baseStart_1815434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815521 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 1, 4]
def baseStart_1815521 : Nat := 118140960795 + 1815521 * 2 ^ 59
def prefixEnd_1815521 : Nat := 4983230072969 + 3 ^ 40 * 1815521 * 2
def baseEnd_1815521 : Nat := 310744970443832166479359

theorem tailTrace_1815521 : CollatzResearch.WordTrace tailWord_1815521 prefixEnd_1815521 310744970443832166479359 := by
  unfold tailWord_1815521
  simp only [CollatzResearch.WordTrace]
  refine ⟨66217490855684958146270417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44144993903789972097513611 66217490855684958146270417)
  ·
    refine ⟨49663118141763718609702813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66217490855684958146270417 49663118141763718609702813)
    ·
      refine ⟨18623669303161394478638555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49663118141763718609702813 18623669303161394478638555)
      ·
        refine ⟨27935503954742091717957833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18623669303161394478638555 27935503954742091717957833)
        ·
          refine ⟨20951627966056568788468375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27935503954742091717957833 20951627966056568788468375)
          ·
            refine ⟨31427441949084853182702563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20951627966056568788468375 31427441949084853182702563)
            ·
              refine ⟨47141162923627279774053845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31427441949084853182702563 47141162923627279774053845)
              ·
                refine ⟨1104871006022514369704387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47141162923627279774053845 1104871006022514369704387)
                ·
                  refine ⟨1657306509033771554556581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104871006022514369704387 1657306509033771554556581)
                  ·
                    refine ⟨310744970443832166479359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657306509033771554556581 310744970443832166479359)
                    ·
                      rfl

theorem cell23_1815521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_1815521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815521 prefixEnd_1815521 := by exact prefixLift 1815521
  have htrace : WordTrace (prefixWord ++ tailWord_1815521) baseStart_1815521 baseEnd_1815521 := by
    simpa [prefixWord, tailWord_1815521, baseEnd_1815521] using wordTrace_append hprefix tailTrace_1815521
  have hstable : (prefixWord ++ tailWord_1815521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815521).length < 2 ^ (prefixWord ++ tailWord_1815521).sum := by decide
  have hdescent : baseEnd_1815521 < baseStart_1815521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815557 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_1815557 : Nat := 118140960795 + 1815557 * 2 ^ 59
def prefixEnd_1815557 : Nat := 4983230072969 + 3 ^ 40 * 1815557 * 2
def baseEnd_1815557 : Nat := 932253396635058358587911

theorem tailTrace_1815557 : CollatzResearch.WordTrace tailWord_1815557 prefixEnd_1815557 932253396635058358587911 := by
  unfold tailWord_1815557
  simp only [CollatzResearch.WordTrace]
  refine ⟨66218803883554536294580925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44145869255703024196387283 66218803883554536294580925)
  ·
    refine ⟨24832051456332951110467847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66218803883554536294580925 24832051456332951110467847)
    ·
      refine ⟨37248077184499426665701771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24832051456332951110467847 37248077184499426665701771)
      ·
        refine ⟨55872115776749139998552657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37248077184499426665701771 55872115776749139998552657)
        ·
          refine ⟨41904086832561854998914493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55872115776749139998552657 41904086832561854998914493)
          ·
            refine ⟨15714032562210695624592935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41904086832561854998914493 15714032562210695624592935)
            ·
              refine ⟨23571048843316043436889403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15714032562210695624592935 23571048843316043436889403)
              ·
                refine ⟨35356573264974065155334105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23571048843316043436889403 35356573264974065155334105)
                ·
                  refine ⟨26517429948730548866500579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35356573264974065155334105 26517429948730548866500579)
                  ·
                    refine ⟨39776144923095823299750869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26517429948730548866500579 39776144923095823299750869)
                    ·
                      refine ⟨932253396635058358587911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39776144923095823299750869 932253396635058358587911)
                      ·
                        rfl

theorem cell23_1815557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_1815557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815557 prefixEnd_1815557 := by exact prefixLift 1815557
  have htrace : WordTrace (prefixWord ++ tailWord_1815557) baseStart_1815557 baseEnd_1815557 := by
    simpa [prefixWord, tailWord_1815557, baseEnd_1815557] using wordTrace_append hprefix tailTrace_1815557
  have hstable : (prefixWord ++ tailWord_1815557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815557).length < 2 ^ (prefixWord ++ tailWord_1815557).sum := by decide
  have hdescent : baseEnd_1815557 < baseStart_1815557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815564 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_1815564 : Nat := 118140960795 + 1815564 * 2 ^ 59
def prefixEnd_1815564 : Nat := 4983230072969 + 3 ^ 40 * 1815564 * 2
def baseEnd_1815564 : Nat := 310752330333213277066793

theorem tailTrace_1815564 : CollatzResearch.WordTrace tailWord_1815564 prefixEnd_1815564 310752330333213277066793 := by
  unfold tailWord_1815564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33109529597264588245042873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44146039463019450993390497 33109529597264588245042873)
  ·
    refine ⟨24832147197948441183782155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33109529597264588245042873 24832147197948441183782155)
    ·
      refine ⟨37248220796922661775673233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24832147197948441183782155 37248220796922661775673233)
      ·
        refine ⟨27936165597691996331754925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37248220796922661775673233 27936165597691996331754925)
        ·
          refine ⟨10476062099134498624408097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27936165597691996331754925 10476062099134498624408097)
          ·
            refine ⟨7857046574350873968306073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476062099134498624408097 7857046574350873968306073)
            ·
              refine ⟨5892784930763155476229555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7857046574350873968306073 5892784930763155476229555)
              ·
                refine ⟨8839177396144733214344333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892784930763155476229555 8839177396144733214344333)
                ·
                  refine ⟨3314691523554274955379125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8839177396144733214344333 3314691523554274955379125)
                  ·
                    refine ⟨310752330333213277066793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3314691523554274955379125 310752330333213277066793)
                    ·
                      rfl

theorem cell23_1815564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_1815564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815564 prefixEnd_1815564 := by exact prefixLift 1815564
  have htrace : WordTrace (prefixWord ++ tailWord_1815564) baseStart_1815564 baseEnd_1815564 := by
    simpa [prefixWord, tailWord_1815564, baseEnd_1815564] using wordTrace_append hprefix tailTrace_1815564
  have hstable : (prefixWord ++ tailWord_1815564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815564).length < 2 ^ (prefixWord ++ tailWord_1815564).sum := by decide
  have hdescent : baseEnd_1815564 < baseStart_1815564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815567 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_1815567 : Nat := 118140960795 + 1815567 * 2 ^ 59
def prefixEnd_1815567 : Nat := 4983230072969 + 3 ^ 40 * 1815567 * 2
def baseEnd_1815567 : Nat := 932258531441603319462865

theorem tailTrace_1815567 : CollatzResearch.WordTrace tailWord_1815567 prefixEnd_1815567 932258531441603319462865 := by
  unfold tailWord_1815567
  simp only [CollatzResearch.WordTrace]
  refine ⟨66219168613518308002444955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44146112409012205334963303 66219168613518308002444955)
  ·
    refine ⟨99328752920277462003667433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66219168613518308002444955 99328752920277462003667433)
    ·
      refine ⟨74496564690208096502750575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99328752920277462003667433 74496564690208096502750575)
      ·
        refine ⟨111744847035312144754125863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74496564690208096502750575 111744847035312144754125863)
        ·
          refine ⟨167617270552968217131188795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111744847035312144754125863 167617270552968217131188795)
          ·
            refine ⟨251425905829452325696783193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167617270552968217131188795 251425905829452325696783193)
            ·
              refine ⟨188569429372089244272587395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251425905829452325696783193 188569429372089244272587395)
              ·
                refine ⟨282854144058133866408881093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188569429372089244272587395 282854144058133866408881093)
                ·
                  refine ⟨53035152010900099951665205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282854144058133866408881093 53035152010900099951665205)
                  ·
                    refine ⟨4972045501021884370468613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53035152010900099951665205 4972045501021884370468613)
                    ·
                      refine ⟨932258531441603319462865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4972045501021884370468613 932258531441603319462865)
                      ·
                        rfl

theorem cell23_1815567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_1815567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815567 prefixEnd_1815567 := by exact prefixLift 1815567
  have htrace : WordTrace (prefixWord ++ tailWord_1815567) baseStart_1815567 baseEnd_1815567 := by
    simpa [prefixWord, tailWord_1815567, baseEnd_1815567] using wordTrace_append hprefix tailTrace_1815567
  have hstable : (prefixWord ++ tailWord_1815567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815567).length < 2 ^ (prefixWord ++ tailWord_1815567).sum := by decide
  have hdescent : baseEnd_1815567 < baseStart_1815567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815607 : List Nat := [1, 1, 3, 1, 2, 2, 1, 12]
def baseStart_1815607 : Nat := 118140960795 + 1815607 * 2 ^ 59
def prefixEnd_1815607 : Nat := 4983230072969 + 3 ^ 40 * 1815607 * 2
def baseEnd_1815607 : Nat := 34528854469177154183803

theorem tailTrace_1815607 : CollatzResearch.WordTrace tailWord_1815607 prefixEnd_1815607 34528854469177154183803 := by
  unfold tailWord_1815607
  simp only [CollatzResearch.WordTrace]
  refine ⟨66220627533373394833901075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44147085022248929889267383 66220627533373394833901075)
  ·
    refine ⟨99330941300060092250851613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66220627533373394833901075 99330941300060092250851613)
    ·
      refine ⟨37249102987522534594069355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99330941300060092250851613 37249102987522534594069355)
      ·
        refine ⟨55873654481283801891104033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37249102987522534594069355 55873654481283801891104033)
        ·
          refine ⟨41905240860962851418328025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55873654481283801891104033 41905240860962851418328025)
          ·
            refine ⟨31428930645722138563746019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41905240860962851418328025 31428930645722138563746019)
            ·
              refine ⟨47143395968583207845619029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31428930645722138563746019 47143395968583207845619029)
              ·
                refine ⟨34528854469177154183803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 47143395968583207845619029 34528854469177154183803)
                ·
                  rfl

theorem cell23_1815607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 12].length) (baseStart_1815607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815607 prefixEnd_1815607 := by exact prefixLift 1815607
  have htrace : WordTrace (prefixWord ++ tailWord_1815607) baseStart_1815607 baseEnd_1815607 := by
    simpa [prefixWord, tailWord_1815607, baseEnd_1815607] using wordTrace_append hprefix tailTrace_1815607
  have hstable : (prefixWord ++ tailWord_1815607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815607).length < 2 ^ (prefixWord ++ tailWord_1815607).sum := by decide
  have hdescent : baseEnd_1815607 < baseStart_1815607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815621 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_1815621 : Nat := 118140960795 + 1815621 * 2 ^ 59
def prefixEnd_1815621 : Nat := 4983230072969 + 3 ^ 40 * 1815621 * 2
def baseEnd_1815621 : Nat := 932286259396946108187617

theorem tailTrace_1815621 : CollatzResearch.WordTrace tailWord_1815621 prefixEnd_1815621 932286259396946108187617 := by
  unfold tailWord_1815621
  simp only [CollatzResearch.WordTrace]
  refine ⟨66221138155322675224910717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44147425436881783483273811 66221138155322675224910717)
  ·
    refine ⟨24832926808246003209341519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66221138155322675224910717 24832926808246003209341519)
    ·
      refine ⟨37249390212369004814012279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24832926808246003209341519 37249390212369004814012279)
      ·
        refine ⟨55874085318553507221018419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37249390212369004814012279 55874085318553507221018419)
        ·
          refine ⟨83811127977830260831527629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55874085318553507221018419 83811127977830260831527629)
          ·
            refine ⟨31429172991686347811822861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83811127977830260831527629 31429172991686347811822861)
            ·
              refine ⟨11785939871882380429433573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31429172991686347811822861 11785939871882380429433573)
              ·
                refine ⟨2209863725977946330518795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11785939871882380429433573 2209863725977946330518795)
                ·
                  refine ⟨3314795588966919495778193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209863725977946330518795 3314795588966919495778193)
                  ·
                    refine ⟨2486096691725189621833645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3314795588966919495778193 2486096691725189621833645)
                    ·
                      refine ⟨932286259396946108187617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486096691725189621833645 932286259396946108187617)
                      ·
                        rfl

theorem cell23_1815621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_1815621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815621 prefixEnd_1815621 := by exact prefixLift 1815621
  have htrace : WordTrace (prefixWord ++ tailWord_1815621) baseStart_1815621 baseEnd_1815621 := by
    simpa [prefixWord, tailWord_1815621, baseEnd_1815621] using wordTrace_append hprefix tailTrace_1815621
  have hstable : (prefixWord ++ tailWord_1815621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815621).length < 2 ^ (prefixWord ++ tailWord_1815621).sum := by decide
  have hdescent : baseEnd_1815621 < baseStart_1815621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815646 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1815646 : Nat := 118140960795 + 1815646 * 2 ^ 59
def prefixEnd_1815646 : Nat := 4983230072969 + 3 ^ 40 * 1815646 * 2
def baseEnd_1815646 : Nat := 932299096413308510375003

theorem tailTrace_1815646 : CollatzResearch.WordTrace tailWord_1815646 prefixEnd_1815646 932299096413308510375003 := by
  unfold tailWord_1815646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277756247529013061821349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44148033320154736329713861 8277756247529013061821349)
  ·
    refine ⟨1552079296411689949091503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8277756247529013061821349 1552079296411689949091503)
    ·
      refine ⟨2328118944617534923637255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552079296411689949091503 2328118944617534923637255)
      ·
        refine ⟨3492178416926302385455883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328118944617534923637255 3492178416926302385455883)
        ·
          refine ⟨5238267625389453578183825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492178416926302385455883 5238267625389453578183825)
          ·
            refine ⟨3928700719042090183637869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238267625389453578183825 3928700719042090183637869)
            ·
              refine ⟨1473262769640783818864201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3928700719042090183637869 1473262769640783818864201)
              ·
                refine ⟨1104947077230587864148151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473262769640783818864201 1104947077230587864148151)
                ·
                  refine ⟨1657420615845881796222227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104947077230587864148151 1657420615845881796222227)
                  ·
                    refine ⟨2486130923768822694333341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1657420615845881796222227 2486130923768822694333341)
                    ·
                      refine ⟨932299096413308510375003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486130923768822694333341 932299096413308510375003)
                      ·
                        rfl

theorem cell23_1815646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1815646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815646 prefixEnd_1815646 := by exact prefixLift 1815646
  have htrace : WordTrace (prefixWord ++ tailWord_1815646) baseStart_1815646 baseEnd_1815646 := by
    simpa [prefixWord, tailWord_1815646, baseEnd_1815646] using wordTrace_append hprefix tailTrace_1815646
  have hstable : (prefixWord ++ tailWord_1815646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815646).length < 2 ^ (prefixWord ++ tailWord_1815646).sum := by decide
  have hdescent : baseEnd_1815646 < baseStart_1815646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815798 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1815798 : Nat := 118140960795 + 1815798 * 2 ^ 59
def prefixEnd_1815798 : Nat := 4983230072969 + 3 ^ 40 * 1815798 * 2
def baseEnd_1815798 : Nat := 932377145472791915674303

theorem tailTrace_1815798 : CollatzResearch.WordTrace tailWord_1815798 prefixEnd_1815798 932377145472791915674303 := by
  unfold tailWord_1815798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139224617230089653381503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44151729250454289636069365 4139224617230089653381503)
  ·
    refine ⟨6208836925845134480072255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4139224617230089653381503 6208836925845134480072255)
    ·
      refine ⟨9313255388767701720108383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6208836925845134480072255 9313255388767701720108383)
      ·
        refine ⟨13969883083151552580162575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313255388767701720108383 13969883083151552580162575)
        ·
          refine ⟨20954824624727328870243863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13969883083151552580162575 20954824624727328870243863)
          ·
            refine ⟨31432236937090993305365795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20954824624727328870243863 31432236937090993305365795)
            ·
              refine ⟨47148355405636489958048693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31432236937090993305365795 47148355405636489958048693)
              ·
                refine ⟨4420158319278420933567065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47148355405636489958048693 4420158319278420933567065)
                ·
                  refine ⟨3315118739458815700175299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4420158319278420933567065 3315118739458815700175299)
                  ·
                    refine ⟨4972678109188223550262949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315118739458815700175299 4972678109188223550262949)
                    ·
                      refine ⟨932377145472791915674303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4972678109188223550262949 932377145472791915674303)
                      ·
                        rfl

theorem cell23_1815798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1815798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815798 prefixEnd_1815798 := by exact prefixLift 1815798
  have htrace : WordTrace (prefixWord ++ tailWord_1815798) baseStart_1815798 baseEnd_1815798 := by
    simpa [prefixWord, tailWord_1815798, baseEnd_1815798] using wordTrace_append hprefix tailTrace_1815798
  have hstable : (prefixWord ++ tailWord_1815798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815798).length < 2 ^ (prefixWord ++ tailWord_1815798).sum := by decide
  have hdescent : baseEnd_1815798 < baseStart_1815798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815801 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1815801 : Nat := 118140960795 + 1815801 * 2 ^ 59
def prefixEnd_1815801 : Nat := 4983230072969 + 3 ^ 40 * 1815801 * 2
def baseEnd_1815801 : Nat := 932378685914755403936789

theorem tailTrace_1815801 : CollatzResearch.WordTrace tailWord_1815801 prefixEnd_1815801 932378685914755403936789 := by
  unfold tailWord_1815801
  simp only [CollatzResearch.WordTrace]
  refine ⟨66227703294670565966463257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44151802196447043977642171 66227703294670565966463257)
  ·
    refine ⟨49670777471002924474847443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66227703294670565966463257 49670777471002924474847443)
    ·
      refine ⟨74506166206504386712271165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49670777471002924474847443 74506166206504386712271165)
      ·
        refine ⟨27939812327439145017101687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74506166206504386712271165 27939812327439145017101687)
        ·
          refine ⟨41909718491158717525652531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27939812327439145017101687 41909718491158717525652531)
          ·
            refine ⟨62864577736738076288478797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41909718491158717525652531 62864577736738076288478797)
            ·
              refine ⟨23574216651276778608179549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62864577736738076288478797 23574216651276778608179549)
              ·
                refine ⟨8840331244228791978067331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23574216651276778608179549 8840331244228791978067331)
                ·
                  refine ⟨13260496866343187967100997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840331244228791978067331 13260496866343187967100997)
                  ·
                    refine ⟨2486343162439347743831437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13260496866343187967100997 2486343162439347743831437)
                    ·
                      refine ⟨932378685914755403936789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2486343162439347743831437 932378685914755403936789)
                      ·
                        rfl

theorem cell23_1815801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1815801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815801 prefixEnd_1815801 := by exact prefixLift 1815801
  have htrace : WordTrace (prefixWord ++ tailWord_1815801) baseStart_1815801 baseEnd_1815801 := by
    simpa [prefixWord, tailWord_1815801, baseEnd_1815801] using wordTrace_append hprefix tailTrace_1815801
  have hstable : (prefixWord ++ tailWord_1815801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815801).length < 2 ^ (prefixWord ++ tailWord_1815801).sum := by decide
  have hdescent : baseEnd_1815801 < baseStart_1815801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1815876 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1815876 : Nat := 118140960795 + 1815876 * 2 ^ 59
def prefixEnd_1815876 : Nat := 4983230072969 + 3 ^ 40 * 1815876 * 2
def baseEnd_1815876 : Nat := 310805732321280870166315

theorem tailTrace_1815876 : CollatzResearch.WordTrace tailWord_1815876 prefixEnd_1815876 310805732321280870166315 := by
  unfold tailWord_1815876
  simp only [CollatzResearch.WordTrace]
  refine ⟨33115219384699426887721741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44153625846265902516962321 33115219384699426887721741)
  ·
    refine ⟨12418207269262285082895653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33115219384699426887721741 12418207269262285082895653)
    ·
      refine ⟨2328413862986678453042935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12418207269262285082895653 2328413862986678453042935)
      ·
        refine ⟨3492620794480017679564403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328413862986678453042935 3492620794480017679564403)
        ·
          refine ⟨5238931191720026519346605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492620794480017679564403 5238931191720026519346605)
          ·
            refine ⟨1964599196895009944754977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5238931191720026519346605 1964599196895009944754977)
            ·
              refine ⟨1473449397671257458566233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964599196895009944754977 1473449397671257458566233)
              ·
                refine ⟨1105087048253443093924675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473449397671257458566233 1105087048253443093924675)
                ·
                  refine ⟨1657630572380164640887013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105087048253443093924675 1657630572380164640887013)
                  ·
                    refine ⟨310805732321280870166315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657630572380164640887013 310805732321280870166315)
                    ·
                      rfl

theorem cell23_1815876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1815876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1815876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1815876 prefixEnd_1815876 := by exact prefixLift 1815876
  have htrace : WordTrace (prefixWord ++ tailWord_1815876) baseStart_1815876 baseEnd_1815876 := by
    simpa [prefixWord, tailWord_1815876, baseEnd_1815876] using wordTrace_append hprefix tailTrace_1815876
  have hstable : (prefixWord ++ tailWord_1815876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1815876).length < 2 ^ (prefixWord ++ tailWord_1815876).sum := by decide
  have hdescent : baseEnd_1815876 < baseStart_1815876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1815876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
