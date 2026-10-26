import V185TrunkScan23Chunk0698

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4133091 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 5]
def baseStart_4133091 : Nat := 118140960795 + 4133091 * 2 ^ 59
def prefixEnd_4133091 : Nat := 4983230072969 + 3 ^ 40 * 4133091 * 2
def baseEnd_4133091 : Nat := 235806919085777110683863

theorem tailTrace_4133091 : CollatzResearch.WordTrace tailWord_4133091 prefixEnd_4133091 235806919085777110683863 := by
  unfold tailWord_4133091
  simp only [CollatzResearch.WordTrace]
  refine ⟨150746213069524657590271127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100497475379683105060180751 150746213069524657590271127)
  ·
    refine ⟨226119319604286986385406691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150746213069524657590271127 226119319604286986385406691)
    ·
      refine ⟨339178979406430479578110037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226119319604286986385406691 339178979406430479578110037)
      ·
        refine ⟨3974753664919107182555977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 339178979406430479578110037 3974753664919107182555977)
        ·
          refine ⟨2981065248689330386916983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3974753664919107182555977 2981065248689330386916983)
          ·
            refine ⟨4471597873033995580375475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981065248689330386916983 4471597873033995580375475)
            ·
              refine ⟨6707396809550993370563213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471597873033995580375475 6707396809550993370563213)
              ·
                refine ⟨2515273803581622513961205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707396809550993370563213 2515273803581622513961205)
                ·
                  refine ⟨235806919085777110683863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2515273803581622513961205 235806919085777110683863)
                  ·
                    rfl

theorem cell23_4133091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 5].length) (baseStart_4133091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133091 prefixEnd_4133091 := by exact prefixLift 4133091
  have htrace : WordTrace (prefixWord ++ tailWord_4133091) baseStart_4133091 baseEnd_4133091 := by
    simpa [prefixWord, tailWord_4133091, baseEnd_4133091] using wordTrace_append hprefix tailTrace_4133091
  have hstable : (prefixWord ++ tailWord_4133091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133091).length < 2 ^ (prefixWord ++ tailWord_4133091).sum := by decide
  have hdescent : baseEnd_4133091 < baseStart_4133091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133117 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_4133117 : Nat := 118140960795 + 4133117 * 2 ^ 59
def prefixEnd_4133117 : Nat := 4983230072969 + 3 ^ 40 * 4133117 * 2
def baseEnd_4133117 : Nat := 707425207423003631476549

theorem tailTrace_4133117 : CollatzResearch.WordTrace tailWord_4133117 prefixEnd_4133117 707425207423003631476549 := by
  unfold tailWord_4133117
  simp only [CollatzResearch.WordTrace]
  refine ⟨150747161367430464030717605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100498107578286976020478403 150747161367430464030717605)
  ·
    refine ⟨28265092756393212005759551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150747161367430464030717605 28265092756393212005759551)
    ·
      refine ⟨42397639134589818008639327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28265092756393212005759551 42397639134589818008639327)
      ·
        refine ⟨63596458701884727012958991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42397639134589818008639327 63596458701884727012958991)
        ·
          refine ⟨95394688052827090519438487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63596458701884727012958991 95394688052827090519438487)
          ·
            refine ⟨143092032079240635779157731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95394688052827090519438487 143092032079240635779157731)
            ·
              refine ⟨214638048118860953668736597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143092032079240635779157731 214638048118860953668736597)
              ·
                refine ⟨2515289626392901800805507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 214638048118860953668736597 2515289626392901800805507)
                ·
                  refine ⟨3772934439589352701208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515289626392901800805507 3772934439589352701208261)
                  ·
                    refine ⟨707425207423003631476549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3772934439589352701208261 707425207423003631476549)
                    ·
                      rfl

theorem cell23_4133117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_4133117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133117 prefixEnd_4133117 := by exact prefixLift 4133117
  have htrace : WordTrace (prefixWord ++ tailWord_4133117) baseStart_4133117 baseEnd_4133117 := by
    simpa [prefixWord, tailWord_4133117, baseEnd_4133117] using wordTrace_append hprefix tailTrace_4133117
  have hstable : (prefixWord ++ tailWord_4133117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133117).length < 2 ^ (prefixWord ++ tailWord_4133117).sum := by decide
  have hdescent : baseEnd_4133117 < baseStart_4133117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133167 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 2, 3, 2]
def baseStart_4133167 : Nat := 118140960795 + 4133167 * 2 ^ 59
def prefixEnd_4133167 : Nat := 4983230072969 + 3 ^ 40 * 4133167 * 2
def baseEnd_4133167 : Nat := 2122301296301735698804417

theorem tailTrace_4133167 : CollatzResearch.WordTrace tailWord_4133167 prefixEnd_4133167 2122301296301735698804417 := by
  unfold tailWord_4133167
  simp only [CollatzResearch.WordTrace]
  refine ⟨150748985017249322570037755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100499323344832881713358503 150748985017249322570037755)
  ·
    refine ⟨226123477525873983855056633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150748985017249322570037755 226123477525873983855056633)
    ·
      refine ⟨169592608144405487891292475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226123477525873983855056633 169592608144405487891292475)
      ·
        refine ⟨254388912216608231836938713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169592608144405487891292475 254388912216608231836938713)
        ·
          refine ⟨190791684162456173877704035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254388912216608231836938713 190791684162456173877704035)
          ·
            refine ⟨286187526243684260816556053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190791684162456173877704035 286187526243684260816556053)
            ·
              refine ⟨13415040292672699725776065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286187526243684260816556053 13415040292672699725776065)
              ·
                refine ⟨10061280219504524794332049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13415040292672699725776065 10061280219504524794332049)
                ·
                  refine ⟨7545960164628393595749037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10061280219504524794332049 7545960164628393595749037)
                  ·
                    refine ⟨2829735061735647598405889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7545960164628393595749037 2829735061735647598405889)
                    ·
                      refine ⟨2122301296301735698804417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829735061735647598405889 2122301296301735698804417)
                      ·
                        rfl

theorem cell23_4133167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3, 2].length) (baseStart_4133167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133167 prefixEnd_4133167 := by exact prefixLift 4133167
  have htrace : WordTrace (prefixWord ++ tailWord_4133167) baseStart_4133167 baseEnd_4133167 := by
    simpa [prefixWord, tailWord_4133167, baseEnd_4133167] using wordTrace_append hprefix tailTrace_4133167
  have hstable : (prefixWord ++ tailWord_4133167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133167).length < 2 ^ (prefixWord ++ tailWord_4133167).sum := by decide
  have hdescent : baseEnd_4133167 < baseStart_4133167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133180 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_4133180 : Nat := 118140960795 + 4133180 * 2 ^ 59
def prefixEnd_4133180 : Nat := 4983230072969 + 3 ^ 40 * 4133180 * 2
def baseEnd_4133180 : Nat := 2122307971550244147941857

theorem tailTrace_4133180 : CollatzResearch.WordTrace tailWord_4133180 prefixEnd_4133180 2122307971550244147941857 := by
  unfold tailWord_4133180
  simp only [CollatzResearch.WordTrace]
  refine ⟨75374729583101112895130497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100499639444134817193507329 75374729583101112895130497)
  ·
    refine ⟨56531047187325834671347873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75374729583101112895130497 56531047187325834671347873)
    ·
      refine ⟨42398285390494376003510905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56531047187325834671347873 42398285390494376003510905)
      ·
        refine ⟨31798714042870782002633179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42398285390494376003510905 31798714042870782002633179)
        ·
          refine ⟨47698071064306173003949769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31798714042870782002633179 47698071064306173003949769)
          ·
            refine ⟨35773553298229629752962327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47698071064306173003949769 35773553298229629752962327)
            ·
              refine ⟨53660329947344444629443491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35773553298229629752962327 53660329947344444629443491)
              ·
                refine ⟨80490494921016666944165237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53660329947344444629443491 80490494921016666944165237)
                ·
                  refine ⟨7545983898845312526015491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80490494921016666944165237 7545983898845312526015491)
                  ·
                    refine ⟨11318975848267968789023237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7545983898845312526015491 11318975848267968789023237)
                    ·
                      refine ⟨2122307971550244147941857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11318975848267968789023237 2122307971550244147941857)
                      ·
                        rfl

theorem cell23_4133180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_4133180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133180 prefixEnd_4133180 := by exact prefixLift 4133180
  have htrace : WordTrace (prefixWord ++ tailWord_4133180) baseStart_4133180 baseEnd_4133180 := by
    simpa [prefixWord, tailWord_4133180, baseEnd_4133180] using wordTrace_append hprefix tailTrace_4133180
  have hstable : (prefixWord ++ tailWord_4133180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133180).length < 2 ^ (prefixWord ++ tailWord_4133180).sum := by decide
  have hdescent : baseEnd_4133180 < baseStart_4133180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133224 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_4133224 : Nat := 118140960795 + 4133224 * 2 ^ 59
def prefixEnd_4133224 : Nat := 4983230072969 + 3 ^ 40 * 4133224 * 2
def baseEnd_4133224 : Nat := 707443521566347325263885

theorem tailTrace_4133224 : CollatzResearch.WordTrace tailWord_4133224 prefixEnd_4133224 707443521566347325263885 := by
  unfold tailWord_4133224
  simp only [CollatzResearch.WordTrace]
  refine ⟨75375531989021410652431363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100500709318695214203241817 75375531989021410652431363)
  ·
    refine ⟨113063297983532115978647045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75375531989021410652431363 113063297983532115978647045)
    ·
      refine ⟨21199368371912271745996321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113063297983532115978647045 21199368371912271745996321)
      ·
        refine ⟨15899526278934203809497241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21199368371912271745996321 15899526278934203809497241)
        ·
          refine ⟨11924644709200652857122931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15899526278934203809497241 11924644709200652857122931)
          ·
            refine ⟨17886967063800979285684397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924644709200652857122931 17886967063800979285684397)
            ·
              refine ⟨6707612648925367232131649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17886967063800979285684397 6707612648925367232131649)
              ·
                refine ⟨5030709486694025424098737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707612648925367232131649 5030709486694025424098737)
                ·
                  refine ⟨3773032115020519068074053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030709486694025424098737 3773032115020519068074053)
                  ·
                    refine ⟨707443521566347325263885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773032115020519068074053 707443521566347325263885)
                    ·
                      rfl

theorem cell23_4133224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_4133224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133224 prefixEnd_4133224 := by exact prefixLift 4133224
  have htrace : WordTrace (prefixWord ++ tailWord_4133224) baseStart_4133224 baseEnd_4133224 := by
    simpa [prefixWord, tailWord_4133224, baseEnd_4133224] using wordTrace_append hprefix tailTrace_4133224
  have hstable : (prefixWord ++ tailWord_4133224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133224).length < 2 ^ (prefixWord ++ tailWord_4133224).sum := by decide
  have hdescent : baseEnd_4133224 < baseStart_4133224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133260 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_4133260 : Nat := 118140960795 + 4133260 * 2 ^ 59
def prefixEnd_4133260 : Nat := 4983230072969 + 3 ^ 40 * 4133260 * 2
def baseEnd_4133260 : Nat := 2122349050002603834941489

theorem tailTrace_4133260 : CollatzResearch.WordTrace tailWord_4133260 prefixEnd_4133260 2122349050002603834941489 := by
  unfold tailWord_4133260
  simp only [CollatzResearch.WordTrace]
  refine ⟨75376188502956199726586617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100501584670608266302115489 75376188502956199726586617)
  ·
    refine ⟨56532141377217149794939963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75376188502956199726586617 56532141377217149794939963)
    ·
      refine ⟨84798212065825724692409945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56532141377217149794939963 84798212065825724692409945)
      ·
        refine ⟨63598659049369293519307459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84798212065825724692409945 63598659049369293519307459)
        ·
          refine ⟨95397988574053940278961189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63598659049369293519307459 95397988574053940278961189)
          ·
            refine ⟨17887122857635113802305223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95397988574053940278961189 17887122857635113802305223)
            ·
              refine ⟨26830684286452670703457835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17887122857635113802305223 26830684286452670703457835)
              ·
                refine ⟨40246026429679006055186753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26830684286452670703457835 40246026429679006055186753)
                ·
                  refine ⟨30184519822259254541390065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40246026429679006055186753 30184519822259254541390065)
                  ·
                    refine ⟨22638389866694440906042549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30184519822259254541390065 22638389866694440906042549)
                    ·
                      refine ⟨2122349050002603834941489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22638389866694440906042549 2122349050002603834941489)
                      ·
                        rfl

theorem cell23_4133260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_4133260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133260 prefixEnd_4133260 := by exact prefixLift 4133260
  have htrace : WordTrace (prefixWord ++ tailWord_4133260) baseStart_4133260 baseEnd_4133260 := by
    simpa [prefixWord, tailWord_4133260, baseEnd_4133260] using wordTrace_append hprefix tailTrace_4133260
  have hstable : (prefixWord ++ tailWord_4133260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133260).length < 2 ^ (prefixWord ++ tailWord_4133260).sum := by decide
  have hdescent : baseEnd_4133260 < baseStart_4133260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133308 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4133308 : Nat := 118140960795 + 4133308 * 2 ^ 59
def prefixEnd_4133308 : Nat := 4983230072969 + 3 ^ 40 * 4133308 * 2
def baseEnd_4133308 : Nat := 2122373697074019647141269

theorem tailTrace_4133308 : CollatzResearch.WordTrace tailWord_4133308 prefixEnd_4133308 2122373697074019647141269 := by
  unfold tailWord_4133308
  simp only [CollatzResearch.WordTrace]
  refine ⟨75377063854869251825460289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100502751806492335767280385 75377063854869251825460289)
  ·
    refine ⟨56532797891151938869095217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75377063854869251825460289 56532797891151938869095217)
    ·
      refine ⟨42399598418363954151821413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56532797891151938869095217 42399598418363954151821413)
      ·
        refine ⟨7949924703443241403466515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42399598418363954151821413 7949924703443241403466515)
        ·
          refine ⟨11924887055164862105199773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949924703443241403466515 11924887055164862105199773)
          ·
            refine ⟨4471832645686823289449915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11924887055164862105199773 4471832645686823289449915)
            ·
              refine ⟨6707748968530234934174873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471832645686823289449915 6707748968530234934174873)
              ·
                refine ⟨5030811726397676200631155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707748968530234934174873 5030811726397676200631155)
                ·
                  refine ⟨7546217589596514300946733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030811726397676200631155 7546217589596514300946733)
                  ·
                    refine ⟨2829831596098692862855025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7546217589596514300946733 2829831596098692862855025)
                    ·
                      refine ⟨2122373697074019647141269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829831596098692862855025 2122373697074019647141269)
                      ·
                        rfl

theorem cell23_4133308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4133308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133308 prefixEnd_4133308 := by exact prefixLift 4133308
  have htrace : WordTrace (prefixWord ++ tailWord_4133308) baseStart_4133308 baseEnd_4133308 := by
    simpa [prefixWord, tailWord_4133308, baseEnd_4133308] using wordTrace_append hprefix tailTrace_4133308
  have hstable : (prefixWord ++ tailWord_4133308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133308).length < 2 ^ (prefixWord ++ tailWord_4133308).sum := by decide
  have hdescent : baseEnd_4133308 < baseStart_4133308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133327 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 5]
def baseStart_4133327 : Nat := 118140960795 + 4133327 * 2 ^ 59
def prefixEnd_4133327 : Nat := 4983230072969 + 3 ^ 40 * 4133327 * 2
def baseEnd_4133327 : Nat := 235820383689606119200409

theorem tailTrace_4133327 : CollatzResearch.WordTrace tailWord_4133327 prefixEnd_4133327 235820383689606119200409 := by
  unfold tailWord_4133327
  simp only [CollatzResearch.WordTrace]
  refine ⟨150754820696669669895862235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100503213797779779930574823 150754820696669669895862235)
  ·
    refine ⟨226132231045004504843793353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150754820696669669895862235 226132231045004504843793353)
    ·
      refine ⟨169599173283753378632845015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226132231045004504843793353 169599173283753378632845015)
      ·
        refine ⟨254398759925630067949267523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169599173283753378632845015 254398759925630067949267523)
        ·
          refine ⟨381598139888445101923901285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254398759925630067949267523 381598139888445101923901285)
          ·
            refine ⟨71549651229083456610731491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381598139888445101923901285 71549651229083456610731491)
            ·
              refine ⟨107324476843625184916097237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71549651229083456610731491 107324476843625184916097237)
              ·
                refine ⟨2515417426022465271471029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107324476843625184916097237 2515417426022465271471029)
                ·
                  refine ⟨235820383689606119200409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2515417426022465271471029 235820383689606119200409)
                  ·
                    rfl

theorem cell23_4133327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 5].length) (baseStart_4133327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133327 prefixEnd_4133327 := by exact prefixLift 4133327
  have htrace : WordTrace (prefixWord ++ tailWord_4133327) baseStart_4133327 baseEnd_4133327 := by
    simpa [prefixWord, tailWord_4133327, baseEnd_4133327] using wordTrace_append hprefix tailTrace_4133327
  have hstable : (prefixWord ++ tailWord_4133327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133327).length < 2 ^ (prefixWord ++ tailWord_4133327).sum := by decide
  have hdescent : baseEnd_4133327 < baseStart_4133327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133334 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4133334 : Nat := 118140960795 + 4133334 * 2 ^ 59
def prefixEnd_4133334 : Nat := 4983230072969 + 3 ^ 40 * 4133334 * 2
def baseEnd_4133334 : Nat := 2122387047571036545416149

theorem tailTrace_4133334 : CollatzResearch.WordTrace tailWord_4133334 prefixEnd_4133334 2122387047571036545416149 := by
  unfold tailWord_4133334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422192250477769380710441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100503384005096206727578037 9422192250477769380710441)
  ·
    refine ⟨7066644187858327035532831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9422192250477769380710441 7066644187858327035532831)
    ·
      refine ⟨10599966281787490553299247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066644187858327035532831 10599966281787490553299247)
      ·
        refine ⟨15899949422681235829948871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599966281787490553299247 15899949422681235829948871)
        ·
          refine ⟨23849924134021853744923307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15899949422681235829948871 23849924134021853744923307)
          ·
            refine ⟨35774886201032780617384961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23849924134021853744923307 35774886201032780617384961)
            ·
              refine ⟨26831164650774585463038721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35774886201032780617384961 26831164650774585463038721)
              ·
                refine ⟨20123373488080939097279041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26831164650774585463038721 20123373488080939097279041)
                ·
                  refine ⟨15092530116060704322959281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20123373488080939097279041 15092530116060704322959281)
                  ·
                    refine ⟨11319397587045528242219461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15092530116060704322959281 11319397587045528242219461)
                    ·
                      refine ⟨2122387047571036545416149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11319397587045528242219461 2122387047571036545416149)
                      ·
                        rfl

theorem cell23_4133334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4133334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133334 prefixEnd_4133334 := by exact prefixLift 4133334
  have htrace : WordTrace (prefixWord ++ tailWord_4133334) baseStart_4133334 baseEnd_4133334 := by
    simpa [prefixWord, tailWord_4133334, baseEnd_4133334] using wordTrace_append hprefix tailTrace_4133334
  have hstable : (prefixWord ++ tailWord_4133334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133334).length < 2 ^ (prefixWord ++ tailWord_4133334).sum := by decide
  have hdescent : baseEnd_4133334 < baseStart_4133334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133337 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_4133337 : Nat := 118140960795 + 4133337 * 2 ^ 59
def prefixEnd_4133337 : Nat := 4983230072969 + 3 ^ 40 * 4133337 * 2
def baseEnd_4133337 : Nat := 2122388588013000033678635

theorem tailTrace_4133337 : CollatzResearch.WordTrace tailWord_4133337 prefixEnd_4133337 2122388588013000033678635 := by
  unfold tailWord_4133337
  simp only [CollatzResearch.WordTrace]
  refine ⟨150755185426633441603726265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100503456951088961069150843 150755185426633441603726265)
  ·
    refine ⟨113066389069975081202794699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150755185426633441603726265 113066389069975081202794699)
    ·
      refine ⟨169599583604962621804192049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113066389069975081202794699 169599583604962621804192049)
      ·
        refine ⟨127199687703721966353144037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169599583604962621804192049 127199687703721966353144037)
        ·
          refine ⟨23849941444447868691214507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127199687703721966353144037 23849941444447868691214507)
          ·
            refine ⟨35774912166671803036821761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23849941444447868691214507 35774912166671803036821761)
            ·
              refine ⟨26831184125003852277616321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35774912166671803036821761 26831184125003852277616321)
              ·
                refine ⟨20123388093752889208212241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26831184125003852277616321 20123388093752889208212241)
                ·
                  refine ⟨15092541070314666906159181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20123388093752889208212241 15092541070314666906159181)
                  ·
                    refine ⟨5659702901368000089809693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15092541070314666906159181 5659702901368000089809693)
                    ·
                      refine ⟨2122388588013000033678635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5659702901368000089809693 2122388588013000033678635)
                      ·
                        rfl

theorem cell23_4133337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_4133337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133337 prefixEnd_4133337 := by exact prefixLift 4133337
  have htrace : WordTrace (prefixWord ++ tailWord_4133337) baseStart_4133337 baseEnd_4133337 := by
    simpa [prefixWord, tailWord_4133337, baseEnd_4133337] using wordTrace_append hprefix tailTrace_4133337
  have hstable : (prefixWord ++ tailWord_4133337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133337).length < 2 ^ (prefixWord ++ tailWord_4133337).sum := by decide
  have hdescent : baseEnd_4133337 < baseStart_4133337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133354 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_4133354 : Nat := 118140960795 + 4133354 * 2 ^ 59
def prefixEnd_4133354 : Nat := 4983230072969 + 3 ^ 40 * 4133354 * 2
def baseEnd_4133354 : Nat := 2122397317184126467166057

theorem tailTrace_4133354 : CollatzResearch.WordTrace tailWord_4133354 prefixEnd_4133354 2122397317184126467166057 := by
  unfold tailWord_4133354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37688951366892963376773779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100503870311714569004730077 37688951366892963376773779)
  ·
    refine ⟨56533427050339445065160669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37688951366892963376773779 56533427050339445065160669)
    ·
      refine ⟨21200035143877291899435251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56533427050339445065160669 21200035143877291899435251)
      ·
        refine ⟨31800052715815937849152877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200035143877291899435251 31800052715815937849152877)
        ·
          refine ⟨11925019768430976693432329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31800052715815937849152877 11925019768430976693432329)
          ·
            refine ⟨8943764826323232520074247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925019768430976693432329 8943764826323232520074247)
            ·
              refine ⟨13415647239484848780111371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943764826323232520074247 13415647239484848780111371)
              ·
                refine ⟨20123470859227273170167057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415647239484848780111371 20123470859227273170167057)
                ·
                  refine ⟨15092603144420454877625293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20123470859227273170167057 15092603144420454877625293)
                  ·
                    refine ⟨5659726179157670579109485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15092603144420454877625293 5659726179157670579109485)
                    ·
                      refine ⟨2122397317184126467166057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5659726179157670579109485 2122397317184126467166057)
                      ·
                        rfl

theorem cell23_4133354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_4133354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133354 prefixEnd_4133354 := by exact prefixLift 4133354
  have htrace : WordTrace (prefixWord ++ tailWord_4133354) baseStart_4133354 baseEnd_4133354 := by
    simpa [prefixWord, tailWord_4133354, baseEnd_4133354] using wordTrace_append hprefix tailTrace_4133354
  have hstable : (prefixWord ++ tailWord_4133354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133354).length < 2 ^ (prefixWord ++ tailWord_4133354).sum := by decide
  have hdescent : baseEnd_4133354 < baseStart_4133354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133370 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_4133370 : Nat := 118140960795 + 4133370 * 2 ^ 59
def prefixEnd_4133370 : Nat := 4983230072969 + 3 ^ 40 * 4133370 * 2
def baseEnd_4133370 : Nat := 707468510958199468188661

theorem tailTrace_4133370 : CollatzResearch.WordTrace tailWord_4133370 prefixEnd_4133370 707468510958199468188661 := by
  unfold tailWord_4133370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37689097258878472059919391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100504259357009258826451709 37689097258878472059919391)
  ·
    refine ⟨56533645888317708089879087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37689097258878472059919391 56533645888317708089879087)
    ·
      refine ⟨84800468832476562134818631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56533645888317708089879087 84800468832476562134818631)
      ·
        refine ⟨127200703248714843202227947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84800468832476562134818631 127200703248714843202227947)
        ·
          refine ⟨190801054873072264803341921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127200703248714843202227947 190801054873072264803341921)
          ·
            refine ⟨143100791154804198602506441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190801054873072264803341921 143100791154804198602506441)
            ·
              refine ⟨107325593366103148951879831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143100791154804198602506441 107325593366103148951879831)
              ·
                refine ⟨160988390049154723427819747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107325593366103148951879831 160988390049154723427819747)
                ·
                  refine ⟨241482585073732085141729621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160988390049154723427819747 241482585073732085141729621)
                  ·
                    refine ⟨707468510958199468188661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 241482585073732085141729621 707468510958199468188661)
                    ·
                      rfl

theorem cell23_4133370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_4133370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133370 prefixEnd_4133370 := by exact prefixLift 4133370
  have htrace : WordTrace (prefixWord ++ tailWord_4133370) baseStart_4133370 baseEnd_4133370 := by
    simpa [prefixWord, tailWord_4133370, baseEnd_4133370] using wordTrace_append hprefix tailTrace_4133370
  have hstable : (prefixWord ++ tailWord_4133370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133370).length < 2 ^ (prefixWord ++ tailWord_4133370).sum := by decide
  have hdescent : baseEnd_4133370 < baseStart_4133370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133378 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4133378 : Nat := 118140960795 + 4133378 * 2 ^ 59
def prefixEnd_4133378 : Nat := 4983230072969 + 3 ^ 40 * 4133378 * 2
def baseEnd_4133378 : Nat := 235823293413314930362883

theorem tailTrace_4133378 : CollatzResearch.WordTrace tailWord_4133378 prefixEnd_4133378 235823293413314930362883 := by
  unfold tailWord_4133378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37689170204871226401492197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100504453879656603737312525 37689170204871226401492197)
  ·
    refine ⟨7066719413413354950279787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37689170204871226401492197 7066719413413354950279787)
    ·
      refine ⟨10600079120120032425419681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066719413413354950279787 10600079120120032425419681)
      ·
        refine ⟨7950059340090024319064761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10600079120120032425419681 7950059340090024319064761)
        ·
          refine ⟨5962544505067518239298571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7950059340090024319064761 5962544505067518239298571)
          ·
            refine ⟨8943816757601277358947857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962544505067518239298571 8943816757601277358947857)
            ·
              refine ⟨6707862568200958019210893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943816757601277358947857 6707862568200958019210893)
              ·
                refine ⟨2515448463075359257204085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707862568200958019210893 2515448463075359257204085)
                ·
                  refine ⟨235823293413314930362883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2515448463075359257204085 235823293413314930362883)
                  ·
                    rfl

theorem cell23_4133378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4133378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133378 prefixEnd_4133378 := by exact prefixLift 4133378
  have htrace : WordTrace (prefixWord ++ tailWord_4133378) baseStart_4133378 baseEnd_4133378 := by
    simpa [prefixWord, tailWord_4133378, baseEnd_4133378] using wordTrace_append hprefix tailTrace_4133378
  have hstable : (prefixWord ++ tailWord_4133378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133378).length < 2 ^ (prefixWord ++ tailWord_4133378).sum := by decide
  have hdescent : baseEnd_4133378 < baseStart_4133378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133404 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_4133404 : Nat := 118140960795 + 4133404 * 2 ^ 59
def prefixEnd_4133404 : Nat := 4983230072969 + 3 ^ 40 * 4133404 * 2
def baseEnd_4133404 : Nat := 707474330405617090513609

theorem tailTrace_4133404 : CollatzResearch.WordTrace tailWord_4133404 prefixEnd_4133404 707474330405617090513609 := by
  unfold tailWord_4133404
  simp only [CollatzResearch.WordTrace]
  refine ⟨75378814558695356023207633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100505086078260474697610177 75378814558695356023207633)
  ·
    refine ⟨56534110919021517017405725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75378814558695356023207633 56534110919021517017405725)
    ·
      refine ⟨21200291594633068881527147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56534110919021517017405725 21200291594633068881527147)
      ·
        refine ⟨31800437391949603322290721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200291594633068881527147 31800437391949603322290721)
        ·
          refine ⟨23850328043962202491718041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31800437391949603322290721 23850328043962202491718041)
          ·
            refine ⟨17887746032971651868788531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23850328043962202491718041 17887746032971651868788531)
            ·
              refine ⟨26831619049457477803182797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17887746032971651868788531 26831619049457477803182797)
              ·
                refine ⟨10061857143546554176193549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26831619049457477803182797 10061857143546554176193549)
                ·
                  refine ⟨3773196428829957816072581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10061857143546554176193549 3773196428829957816072581)
                  ·
                    refine ⟨707474330405617090513609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773196428829957816072581 707474330405617090513609)
                    ·
                      rfl

theorem cell23_4133404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_4133404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133404 prefixEnd_4133404 := by exact prefixLift 4133404
  have htrace : WordTrace (prefixWord ++ tailWord_4133404) baseStart_4133404 baseEnd_4133404 := by
    simpa [prefixWord, tailWord_4133404, baseEnd_4133404] using wordTrace_append hprefix tailTrace_4133404
  have hstable : (prefixWord ++ tailWord_4133404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133404).length < 2 ^ (prefixWord ++ tailWord_4133404).sum := by decide
  have hdescent : baseEnd_4133404 < baseStart_4133404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133427 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3]
def baseStart_4133427 : Nat := 118140960795 + 4133427 * 2 ^ 59
def prefixEnd_4133427 : Nat := 4983230072969 + 3 ^ 40 * 4133427 * 2
def baseEnd_4133427 : Nat := 2122434801271904681553221

theorem tailTrace_4133427 : CollatzResearch.WordTrace tailWord_4133427 prefixEnd_4133427 2122434801271904681553221 := by
  unfold tailWord_4133427
  simp only [CollatzResearch.WordTrace]
  refine ⟨150758467996307386974502535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100505645330871591316335023 150758467996307386974502535)
  ·
    refine ⟨226137701994461080461753803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150758467996307386974502535 226137701994461080461753803)
    ·
      refine ⟨339206552991691620692630705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226137701994461080461753803 339206552991691620692630705)
      ·
        refine ⟨254404914743768715519473029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339206552991691620692630705 254404914743768715519473029)
        ·
          refine ⟨47700921514456634159901193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254404914743768715519473029 47700921514456634159901193)
          ·
            refine ⟨35775691135842475619925895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47700921514456634159901193 35775691135842475619925895)
            ·
              refine ⟨53663536703763713429888843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35775691135842475619925895 53663536703763713429888843)
              ·
                refine ⟨80495305055645570144833265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53663536703763713429888843 80495305055645570144833265)
                ·
                  refine ⟨60371478791734177608624949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80495305055645570144833265 60371478791734177608624949)
                  ·
                    refine ⟨5659826136725079150808589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60371478791734177608624949 5659826136725079150808589)
                    ·
                      refine ⟨2122434801271904681553221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5659826136725079150808589 2122434801271904681553221)
                      ·
                        rfl

theorem cell23_4133427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_4133427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133427 prefixEnd_4133427 := by exact prefixLift 4133427
  have htrace : WordTrace (prefixWord ++ tailWord_4133427) baseStart_4133427 baseEnd_4133427 := by
    simpa [prefixWord, tailWord_4133427, baseEnd_4133427] using wordTrace_append hprefix tailTrace_4133427
  have hstable : (prefixWord ++ tailWord_4133427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133427).length < 2 ^ (prefixWord ++ tailWord_4133427).sum := by decide
  have hdescent : baseEnd_4133427 < baseStart_4133427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133461 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4133461 : Nat := 118140960795 + 4133461 * 2 ^ 59
def prefixEnd_4133461 : Nat := 4983230072969 + 3 ^ 40 * 4133461 * 2
def baseEnd_4133461 : Nat := 2122452259614157548528065

theorem tailTrace_4133461 : CollatzResearch.WordTrace tailWord_4133461 prefixEnd_4133461 2122452259614157548528065 := by
  unfold tailWord_4133461
  simp only [CollatzResearch.WordTrace]
  refine ⟨150759708078184210781240237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100506472052122807187493491 150759708078184210781240237)
  ·
    refine ⟨56534890529319079042965089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150759708078184210781240237 56534890529319079042965089)
    ·
      refine ⟨42401167896989309282223817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56534890529319079042965089 42401167896989309282223817)
      ·
        refine ⟨31800875922741981961667863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42401167896989309282223817 31800875922741981961667863)
        ·
          refine ⟨47701313884112972942501795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31800875922741981961667863 47701313884112972942501795)
          ·
            refine ⟨71551970826169459413752693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47701313884112972942501795 71551970826169459413752693)
            ·
              refine ⟨6707997264953386820039315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71551970826169459413752693 6707997264953386820039315)
              ·
                refine ⟨10061995897430080230058973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707997264953386820039315 10061995897430080230058973)
                ·
                  refine ⟨3773248461536280086272115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10061995897430080230058973 3773248461536280086272115)
                  ·
                    refine ⟨5659872692304420129408173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773248461536280086272115 5659872692304420129408173)
                    ·
                      refine ⟨2122452259614157548528065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5659872692304420129408173 2122452259614157548528065)
                      ·
                        rfl

theorem cell23_4133461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4133461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133461 prefixEnd_4133461 := by exact prefixLift 4133461
  have htrace : WordTrace (prefixWord ++ tailWord_4133461) baseStart_4133461 baseEnd_4133461 := by
    simpa [prefixWord, tailWord_4133461, baseEnd_4133461] using wordTrace_append hprefix tailTrace_4133461
  have hstable : (prefixWord ++ tailWord_4133461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133461).length < 2 ^ (prefixWord ++ tailWord_4133461).sum := by decide
  have hdescent : baseEnd_4133461 < baseStart_4133461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133468 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 6]
def baseStart_4133468 : Nat := 118140960795 + 4133468 * 2 ^ 59
def prefixEnd_4133468 : Nat := 4983230072969 + 3 ^ 40 * 4133468 * 2
def baseEnd_4133468 : Nat := 235828428219859891237837

theorem tailTrace_4133468 : CollatzResearch.WordTrace tailWord_4133468 prefixEnd_4133468 235828428219859891237837 := by
  unfold tailWord_4133468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75379981694579425488372529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100506642259439233984496705 75379981694579425488372529)
  ·
    refine ⟨56534986270934569116279397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75379981694579425488372529 56534986270934569116279397)
    ·
      refine ⟨10600309925800231709302387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56534986270934569116279397 10600309925800231709302387)
      ·
        refine ⟨15900464888700347563953581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600309925800231709302387 15900464888700347563953581)
        ·
          refine ⟨5962674333262630336482593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15900464888700347563953581 5962674333262630336482593)
          ·
            refine ⟨4472005749946972752361945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962674333262630336482593 4472005749946972752361945)
            ·
              refine ⟨3354004312460229564271459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472005749946972752361945 3354004312460229564271459)
              ·
                refine ⟨5031006468690344346407189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354004312460229564271459 5031006468690344346407189)
                ·
                  refine ⟨235828428219859891237837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5031006468690344346407189 235828428219859891237837)
                  ·
                    rfl

theorem cell23_4133468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_4133468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133468 prefixEnd_4133468 := by exact prefixLift 4133468
  have htrace : WordTrace (prefixWord ++ tailWord_4133468) baseStart_4133468 baseEnd_4133468 := by
    simpa [prefixWord, tailWord_4133468, baseEnd_4133468] using wordTrace_append hprefix tailTrace_4133468
  have hstable : (prefixWord ++ tailWord_4133468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133468).length < 2 ^ (prefixWord ++ tailWord_4133468).sum := by decide
  have hdescent : baseEnd_4133468 < baseStart_4133468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133484 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_4133484 : Nat := 118140960795 + 4133484 * 2 ^ 59
def prefixEnd_4133484 : Nat := 4983230072969 + 3 ^ 40 * 4133484 * 2
def baseEnd_4133484 : Nat := 2122464069669210958540459

theorem tailTrace_4133484 : CollatzResearch.WordTrace tailWord_4133484 prefixEnd_4133484 2122464069669210958540459 := by
  unfold tailWord_4133484
  simp only [CollatzResearch.WordTrace]
  refine ⟨75380273478550442854663753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100507031304733923806218337 75380273478550442854663753)
  ·
    refine ⟨56535205108912832140997815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75380273478550442854663753 56535205108912832140997815)
    ·
      refine ⟨84802807663369248211496723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56535205108912832140997815 84802807663369248211496723)
      ·
        refine ⟨127204211495053872317245085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84802807663369248211496723 127204211495053872317245085)
        ·
          refine ⟨47701579310645202118966907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127204211495053872317245085 47701579310645202118966907)
          ·
            refine ⟨71552368965967803178450361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47701579310645202118966907 71552368965967803178450361)
            ·
              refine ⟨53664276724475852383837771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71552368965967803178450361 53664276724475852383837771)
              ·
                refine ⟨80496415086713778575756657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53664276724475852383837771 80496415086713778575756657)
                ·
                  refine ⟨60372311315035333931817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80496415086713778575756657 60372311315035333931817493)
                  ·
                    refine ⟨2829952092892281278053945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60372311315035333931817493 2829952092892281278053945)
                    ·
                      refine ⟨2122464069669210958540459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829952092892281278053945 2122464069669210958540459)
                      ·
                        rfl

theorem cell23_4133484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_4133484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133484 prefixEnd_4133484 := by exact prefixLift 4133484
  have htrace : WordTrace (prefixWord ++ tailWord_4133484) baseStart_4133484 baseEnd_4133484 := by
    simpa [prefixWord, tailWord_4133484, baseEnd_4133484] using wordTrace_append hprefix tailTrace_4133484
  have hstable : (prefixWord ++ tailWord_4133484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133484).length < 2 ^ (prefixWord ++ tailWord_4133484).sum := by decide
  have hdescent : baseEnd_4133484 < baseStart_4133484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133487 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_4133487 : Nat := 118140960795 + 4133487 * 2 ^ 59
def prefixEnd_4133487 : Nat := 4983230072969 + 3 ^ 40 * 4133487 * 2
def baseEnd_4133487 : Nat := 2122465610111174446802945

theorem tailTrace_4133487 : CollatzResearch.WordTrace tailWord_4133487 prefixEnd_4133487 2122465610111174446802945 := by
  unfold tailWord_4133487
  simp only [CollatzResearch.WordTrace]
  refine ⟨150760656376090017221686715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100507104250726678147791143 150760656376090017221686715)
  ·
    refine ⟨226140984564135025832530073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150760656376090017221686715 226140984564135025832530073)
    ·
      refine ⟨169605738423101269374397555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226140984564135025832530073 169605738423101269374397555)
      ·
        refine ⟨254408607634651904061596333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169605738423101269374397555 254408607634651904061596333)
        ·
          refine ⟨95403227862994464023098625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254408607634651904061596333 95403227862994464023098625)
          ·
            refine ⟨71552420897245848017323969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95403227862994464023098625 71552420897245848017323969)
            ·
              refine ⟨53664315672934386012992977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71552420897245848017323969 53664315672934386012992977)
              ·
                refine ⟨40248236754700789509744733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53664315672934386012992977 40248236754700789509744733)
                ·
                  refine ⟨15093088783012796066154275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40248236754700789509744733 15093088783012796066154275)
                  ·
                    refine ⟨22639633174519194099231413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15093088783012796066154275 22639633174519194099231413)
                    ·
                      refine ⟨2122465610111174446802945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22639633174519194099231413 2122465610111174446802945)
                      ·
                        rfl

theorem cell23_4133487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_4133487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133487 prefixEnd_4133487 := by exact prefixLift 4133487
  have htrace : WordTrace (prefixWord ++ tailWord_4133487) baseStart_4133487 baseEnd_4133487 := by
    simpa [prefixWord, tailWord_4133487, baseEnd_4133487] using wordTrace_append hprefix tailTrace_4133487
  have hstable : (prefixWord ++ tailWord_4133487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133487).length < 2 ^ (prefixWord ++ tailWord_4133487).sum := by decide
  have hdescent : baseEnd_4133487 < baseStart_4133487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133488 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2]
def baseStart_4133488 : Nat := 118140960795 + 4133488 * 2 ^ 59
def prefixEnd_4133488 : Nat := 4983230072969 + 3 ^ 40 * 4133488 * 2
def baseEnd_4133488 : Nat := 2122466123591828942890441

theorem tailTrace_4133488 : CollatzResearch.WordTrace tailWord_4133488 prefixEnd_4133488 2122466123591828942890441 := by
  unfold tailWord_4133488
  simp only [CollatzResearch.WordTrace]
  refine ⟨75380346424543197196236559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100507128566057596261648745 75380346424543197196236559)
  ·
    refine ⟨113070519636814795794354839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75380346424543197196236559 113070519636814795794354839)
    ·
      refine ⟨169605779455222193691532259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113070519636814795794354839 169605779455222193691532259)
      ·
        refine ⟨254408669182833290537298389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169605779455222193691532259 254408669182833290537298389)
        ·
          refine ⟨5962703183972655246967931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 254408669182833290537298389 5962703183972655246967931)
          ·
            refine ⟨8944054775958982870451897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962703183972655246967931 8944054775958982870451897)
            ·
              refine ⟨6708041081969237152838923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8944054775958982870451897 6708041081969237152838923)
              ·
                refine ⟨10062061622953855729258385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708041081969237152838923 10062061622953855729258385)
                ·
                  refine ⟨7546546217215391796943789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062061622953855729258385 7546546217215391796943789)
                  ·
                    refine ⟨2829954831455771923853921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7546546217215391796943789 2829954831455771923853921)
                    ·
                      refine ⟨2122466123591828942890441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829954831455771923853921 2122466123591828942890441)
                      ·
                        rfl

theorem cell23_4133488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2].length) (baseStart_4133488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133488 prefixEnd_4133488 := by exact prefixLift 4133488
  have htrace : WordTrace (prefixWord ++ tailWord_4133488) baseStart_4133488 baseEnd_4133488 := by
    simpa [prefixWord, tailWord_4133488, baseEnd_4133488] using wordTrace_append hprefix tailTrace_4133488
  have hstable : (prefixWord ++ tailWord_4133488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133488).length < 2 ^ (prefixWord ++ tailWord_4133488).sum := by decide
  have hdescent : baseEnd_4133488 < baseStart_4133488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133504 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_4133504 : Nat := 118140960795 + 4133504 * 2 ^ 59
def prefixEnd_4133504 : Nat := 4983230072969 + 3 ^ 40 * 4133504 * 2
def baseEnd_4133504 : Nat := 2122474339282300880290367

theorem tailTrace_4133504 : CollatzResearch.WordTrace tailWord_4133504 prefixEnd_4133504 2122474339282300880290367 := by
  unfold tailWord_4133504
  simp only [CollatzResearch.WordTrace]
  refine ⟨75380638208514214562527783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100507517611352286083370377 75380638208514214562527783)
  ·
    refine ⟨113070957312771321843791675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75380638208514214562527783 113070957312771321843791675)
    ·
      refine ⟨169606435969156982765687513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113070957312771321843791675 169606435969156982765687513)
      ·
        refine ⟨127204826976867737074265635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169606435969156982765687513 127204826976867737074265635)
        ·
          refine ⟨190807240465301605611398453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127204826976867737074265635 190807240465301605611398453)
          ·
            refine ⟨17888178793622025526068605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190807240465301605611398453 17888178793622025526068605)
            ·
              refine ⟨6708067047608259572275727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17888178793622025526068605 6708067047608259572275727)
              ·
                refine ⟨10062100571412389358413591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708067047608259572275727 10062100571412389358413591)
                ·
                  refine ⟨15093150857118584037620387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062100571412389358413591 15093150857118584037620387)
                  ·
                    refine ⟨22639726285677876056430581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15093150857118584037620387 22639726285677876056430581)
                    ·
                      refine ⟨2122474339282300880290367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22639726285677876056430581 2122474339282300880290367)
                      ·
                        rfl

theorem cell23_4133504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_4133504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133504 prefixEnd_4133504 := by exact prefixLift 4133504
  have htrace : WordTrace (prefixWord ++ tailWord_4133504) baseStart_4133504 baseEnd_4133504 := by
    simpa [prefixWord, tailWord_4133504, baseEnd_4133504] using wordTrace_append hprefix tailTrace_4133504
  have hstable : (prefixWord ++ tailWord_4133504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133504).length < 2 ^ (prefixWord ++ tailWord_4133504).sum := by decide
  have hdescent : baseEnd_4133504 < baseStart_4133504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133506 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4133506 : Nat := 118140960795 + 4133506 * 2 ^ 59
def prefixEnd_4133506 : Nat := 4983230072969 + 3 ^ 40 * 4133506 * 2
def baseEnd_4133506 : Nat := 707491788747869957488453

theorem tailTrace_4133506 : CollatzResearch.WordTrace tailWord_4133506 prefixEnd_4133506 707491788747869957488453 := by
  unfold tailWord_4133506
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690337340755295866657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100507566242014122311085581 37690337340755295866657093)
  ·
    refine ⟨7066938251391617974998205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37690337340755295866657093 7066938251391617974998205)
    ·
      refine ⟨2650101844271856740624327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7066938251391617974998205 2650101844271856740624327)
      ·
        refine ⟨3975152766407785110936491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650101844271856740624327 3975152766407785110936491)
        ·
          refine ⟨5962729149611677666404737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975152766407785110936491 5962729149611677666404737)
          ·
            refine ⟨4472046862208758249803553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962729149611677666404737 4472046862208758249803553)
            ·
              refine ⟨3354035146656568687352665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472046862208758249803553 3354035146656568687352665)
              ·
                refine ⟨2515526359992426515514499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354035146656568687352665 2515526359992426515514499)
                ·
                  refine ⟨3773289539988639773271749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515526359992426515514499 3773289539988639773271749)
                  ·
                    refine ⟨707491788747869957488453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773289539988639773271749 707491788747869957488453)
                    ·
                      rfl

theorem cell23_4133506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4133506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133506 prefixEnd_4133506 := by exact prefixLift 4133506
  have htrace : WordTrace (prefixWord ++ tailWord_4133506) baseStart_4133506 baseEnd_4133506 := by
    simpa [prefixWord, tailWord_4133506, baseEnd_4133506] using wordTrace_append hprefix tailTrace_4133506
  have hstable : (prefixWord ++ tailWord_4133506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133506).length < 2 ^ (prefixWord ++ tailWord_4133506).sum := by decide
  have hdescent : baseEnd_4133506 < baseStart_4133506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133511 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 2, 4]
def baseStart_4133511 : Nat := 118140960795 + 4133511 * 2 ^ 59
def prefixEnd_4133511 : Nat := 4983230072969 + 3 ^ 40 * 4133511 * 2
def baseEnd_4133511 : Nat := 707492644548960784300945

theorem tailTrace_4133511 : CollatzResearch.WordTrace tailWord_4133511 prefixEnd_4133511 707492644548960784300945 := by
  unfold tailWord_4133511
  simp only [CollatzResearch.WordTrace]
  refine ⟨150761531728003069320560387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100507687818668712880373591 150761531728003069320560387)
  ·
    refine ⟨226142297592004603980840581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150761531728003069320560387 226142297592004603980840581)
    ·
      refine ⟨42401680798500863246407609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226142297592004603980840581 42401680798500863246407609)
      ·
        refine ⟨31801260598875647434805707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42401680798500863246407609 31801260598875647434805707)
        ·
          refine ⟨47701890898313471152208561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31801260598875647434805707 47701890898313471152208561)
          ·
            refine ⟨35776418173735103364156421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47701890898313471152208561 35776418173735103364156421)
            ·
              refine ⟨6708078407575331880779329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35776418173735103364156421 6708078407575331880779329)
              ·
                refine ⟨5031058805681498910584497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6708078407575331880779329 5031058805681498910584497)
                ·
                  refine ⟨3773294104261124182938373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031058805681498910584497 3773294104261124182938373)
                  ·
                    refine ⟨707492644548960784300945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773294104261124182938373 707492644548960784300945)
                    ·
                      rfl

theorem cell23_4133511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_4133511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133511 prefixEnd_4133511 := by exact prefixLift 4133511
  have htrace : WordTrace (prefixWord ++ tailWord_4133511) baseStart_4133511 baseEnd_4133511 := by
    simpa [prefixWord, tailWord_4133511, baseEnd_4133511] using wordTrace_append hprefix tailTrace_4133511
  have hstable : (prefixWord ++ tailWord_4133511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133511).length < 2 ^ (prefixWord ++ tailWord_4133511).sum := by decide
  have hdescent : baseEnd_4133511 < baseStart_4133511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133518 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4133518 : Nat := 118140960795 + 4133518 * 2 ^ 59
def prefixEnd_4133518 : Nat := 4983230072969 + 3 ^ 40 * 4133518 * 2
def baseEnd_4133518 : Nat := 2122481528011463825515303

theorem tailTrace_4133518 : CollatzResearch.WordTrace tailWord_4133518 prefixEnd_4133518 2122481528011463825515303 := by
  unfold tailWord_4133518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18845223379872213689508151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100507858025985139677376805 18845223379872213689508151)
  ·
    refine ⟨28267835069808320534262227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18845223379872213689508151 28267835069808320534262227)
    ·
      refine ⟨42401752604712480801393341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28267835069808320534262227 42401752604712480801393341)
      ·
        refine ⟨15900657226767180300522503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42401752604712480801393341 15900657226767180300522503)
        ·
          refine ⟨23850985840150770450783755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900657226767180300522503 23850985840150770450783755)
          ·
            refine ⟨35776478760226155676175633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850985840150770450783755 35776478760226155676175633)
            ·
              refine ⟨26832359070169616757131725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35776478760226155676175633 26832359070169616757131725)
              ·
                refine ⟨10062134651313606283924397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26832359070169616757131725 10062134651313606283924397)
                ·
                  refine ⟨3773300494242602356471649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10062134651313606283924397 3773300494242602356471649)
                  ·
                    refine ⟨2829975370681951767353737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3773300494242602356471649 2829975370681951767353737)
                    ·
                      refine ⟨2122481528011463825515303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2829975370681951767353737 2122481528011463825515303)
                      ·
                        rfl

theorem cell23_4133518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4133518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133518 prefixEnd_4133518 := by exact prefixLift 4133518
  have htrace : WordTrace (prefixWord ++ tailWord_4133518) baseStart_4133518 baseEnd_4133518 := by
    simpa [prefixWord, tailWord_4133518, baseEnd_4133518] using wordTrace_append hprefix tailTrace_4133518
  have hstable : (prefixWord ++ tailWord_4133518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133518).length < 2 ^ (prefixWord ++ tailWord_4133518).sum := by decide
  have hdescent : baseEnd_4133518 < baseStart_4133518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133568 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3]
def baseStart_4133568 : Nat := 118140960795 + 4133568 * 2 ^ 59
def prefixEnd_4133568 : Nat := 4983230072969 + 3 ^ 40 * 4133568 * 2
def baseEnd_4133568 : Nat := 2122507202044188629890073

theorem tailTrace_4133568 : CollatzResearch.WordTrace tailWord_4133568 prefixEnd_4133568 2122507202044188629890073 := by
  unfold tailWord_4133568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75381805344398284027692679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100509073792531045370256905 75381805344398284027692679)
  ·
    refine ⟨113072708016597426041539019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75381805344398284027692679 113072708016597426041539019)
    ·
      refine ⟨169609062024896139062308529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113072708016597426041539019 169609062024896139062308529)
      ·
        refine ⟨127206796518672104296731397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169609062024896139062308529 127206796518672104296731397)
        ·
          refine ⟨23851274347251019555637137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127206796518672104296731397 23851274347251019555637137)
          ·
            refine ⟨17888455760438264666727853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23851274347251019555637137 17888455760438264666727853)
            ·
              refine ⟨6708170910164349250022945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17888455760438264666727853 6708170910164349250022945)
              ·
                refine ⟨5031128182623261937517209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6708170910164349250022945 5031128182623261937517209)
                ·
                  refine ⟨3773346136967446453137907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031128182623261937517209 3773346136967446453137907)
                  ·
                    refine ⟨5660019205451169679706861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773346136967446453137907 5660019205451169679706861)
                    ·
                      refine ⟨2122507202044188629890073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660019205451169679706861 2122507202044188629890073)
                      ·
                        rfl

theorem cell23_4133568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_4133568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133568 prefixEnd_4133568 := by exact prefixLift 4133568
  have htrace : WordTrace (prefixWord ++ tailWord_4133568) baseStart_4133568 baseEnd_4133568 := by
    simpa [prefixWord, tailWord_4133568, baseEnd_4133568] using wordTrace_append hprefix tailTrace_4133568
  have hstable : (prefixWord ++ tailWord_4133568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133568).length < 2 ^ (prefixWord ++ tailWord_4133568).sum := by decide
  have hdescent : baseEnd_4133568 < baseStart_4133568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133594 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_4133594 : Nat := 118140960795 + 4133594 * 2 ^ 59
def prefixEnd_4133594 : Nat := 4983230072969 + 3 ^ 40 * 4133594 * 2
def baseEnd_4133594 : Nat := 2122520552541205528164953

theorem tailTrace_4133594 : CollatzResearch.WordTrace tailWord_4133594 prefixEnd_4133594 2122520552541205528164953 := by
  unfold tailWord_4133594
  simp only [CollatzResearch.WordTrace]
  refine ⟨37691139746675593623957959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100509705991134916330554557 37691139746675593623957959)
  ·
    refine ⟨56536709620013390435936939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37691139746675593623957959 56536709620013390435936939)
    ·
      refine ⟨84805064430020085653905409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56536709620013390435936939 84805064430020085653905409)
      ·
        refine ⟨63603798322515064240429057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84805064430020085653905409 63603798322515064240429057)
        ·
          refine ⟨47702848741886298180321793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63603798322515064240429057 47702848741886298180321793)
          ·
            refine ⟨35777136556414723635241345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47702848741886298180321793 35777136556414723635241345)
            ·
              refine ⟨26832852417311042726431009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35777136556414723635241345 26832852417311042726431009)
              ·
                refine ⟨20124639312983282044823257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26832852417311042726431009 20124639312983282044823257)
                ·
                  refine ⟨15093479484737461533617443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20124639312983282044823257 15093479484737461533617443)
                  ·
                    refine ⟨22640219227106192300426165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15093479484737461533617443 22640219227106192300426165)
                    ·
                      refine ⟨2122520552541205528164953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22640219227106192300426165 2122520552541205528164953)
                      ·
                        rfl

theorem cell23_4133594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_4133594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133594 prefixEnd_4133594 := by exact prefixLift 4133594
  have htrace : WordTrace (prefixWord ++ tailWord_4133594) baseStart_4133594 baseEnd_4133594 := by
    simpa [prefixWord, tailWord_4133594, baseEnd_4133594] using wordTrace_append hprefix tailTrace_4133594
  have hstable : (prefixWord ++ tailWord_4133594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133594).length < 2 ^ (prefixWord ++ tailWord_4133594).sum := by decide
  have hdescent : baseEnd_4133594 < baseStart_4133594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133644 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_4133644 : Nat := 118140960795 + 4133644 * 2 ^ 59
def prefixEnd_4133644 : Nat := 4983230072969 + 3 ^ 40 * 4133644 * 2
def baseEnd_4133644 : Nat := 707515408857976777513241

theorem tailTrace_4133644 : CollatzResearch.WordTrace tailWord_4133644 prefixEnd_4133644 707515408857976777513241 := by
  unfold tailWord_4133644
  simp only [CollatzResearch.WordTrace]
  refine ⟨75383191318260616517575993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100510921757680822023434657 75383191318260616517575993)
  ·
    refine ⟨56537393488695462388181995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75383191318260616517575993 56537393488695462388181995)
    ·
      refine ⟨84806090233043193582272993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56537393488695462388181995 84806090233043193582272993)
      ·
        refine ⟨63604567674782395186704745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84806090233043193582272993 63604567674782395186704745)
        ·
          refine ⟨47703425756086796390028559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63604567674782395186704745 47703425756086796390028559)
          ·
            refine ⟨71555138634130194585042839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47703425756086796390028559 71555138634130194585042839)
            ·
              refine ⟨107332707951195291877564259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71555138634130194585042839 107332707951195291877564259)
              ·
                refine ⟨160999061926792937816346389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107332707951195291877564259 160999061926792937816346389)
                ·
                  refine ⟨7546831027818418960141237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160999061926792937816346389 7546831027818418960141237)
                  ·
                    refine ⟨707515408857976777513241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7546831027818418960141237 707515408857976777513241)
                    ·
                      rfl

theorem cell23_4133644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_4133644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133644 prefixEnd_4133644 := by exact prefixLift 4133644
  have htrace : WordTrace (prefixWord ++ tailWord_4133644) baseStart_4133644 baseEnd_4133644 := by
    simpa [prefixWord, tailWord_4133644, baseEnd_4133644] using wordTrace_append hprefix tailTrace_4133644
  have hstable : (prefixWord ++ tailWord_4133644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133644).length < 2 ^ (prefixWord ++ tailWord_4133644).sum := by decide
  have hdescent : baseEnd_4133644 < baseStart_4133644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133678 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4133678 : Nat := 118140960795 + 4133678 * 2 ^ 59
def prefixEnd_4133678 : Nat := 4983230072969 + 3 ^ 40 * 4133678 * 2
def baseEnd_4133678 : Nat := 707521228305394399838189

theorem tailTrace_4133678 : CollatzResearch.WordTrace tailWord_4133678 prefixEnd_4133678 707521228305394399838189 := by
  unfold tailWord_4133678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18845952839799757105236211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100511748478932037894593125 18845952839799757105236211)
  ·
    refine ⟨28268929259699635657854317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18845952839799757105236211 28268929259699635657854317)
    ·
      refine ⟨10600848472387363371695369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28268929259699635657854317 10600848472387363371695369)
      ·
        refine ⟨7950636354290522528771527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10600848472387363371695369 7950636354290522528771527)
        ·
          refine ⟨11925954531435783793157291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950636354290522528771527 11925954531435783793157291)
          ·
            refine ⟨17888931797153675689735937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11925954531435783793157291 17888931797153675689735937)
            ·
              refine ⟨13416698847865256767301953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17888931797153675689735937 13416698847865256767301953)
              ·
                refine ⟨10062524135898942575476465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13416698847865256767301953 10062524135898942575476465)
                ·
                  refine ⟨7546893101924206931607349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062524135898942575476465 7546893101924206931607349)
                  ·
                    refine ⟨707521228305394399838189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7546893101924206931607349 707521228305394399838189)
                    ·
                      rfl

theorem cell23_4133678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4133678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133678 prefixEnd_4133678 := by exact prefixLift 4133678
  have htrace : WordTrace (prefixWord ++ tailWord_4133678) baseStart_4133678 baseEnd_4133678 := by
    simpa [prefixWord, tailWord_4133678, baseEnd_4133678] using wordTrace_append hprefix tailTrace_4133678
  have hstable : (prefixWord ++ tailWord_4133678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133678).length < 2 ^ (prefixWord ++ tailWord_4133678).sum := by decide
  have hdescent : baseEnd_4133678 < baseStart_4133678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133681 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4133681 : Nat := 118140960795 + 4133681 * 2 ^ 59
def prefixEnd_4133681 : Nat := 4983230072969 + 3 ^ 40 * 4133681 * 2
def baseEnd_4133681 : Nat := 2122565225358146687777053

theorem tailTrace_4133681 : CollatzResearch.WordTrace tailWord_4133681 prefixEnd_4133681 2122565225358146687777053 := by
  unfold tailWord_4133681
  simp only [CollatzResearch.WordTrace]
  refine ⟨150767732137387188354248897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100511821424924792236165931 150767732137387188354248897)
  ·
    refine ⟨113075799103040391265686673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150767732137387188354248897 113075799103040391265686673)
    ·
      refine ⟨84806849327280293449265005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113075799103040391265686673 84806849327280293449265005)
      ·
        refine ⟨31802568497730110043474377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84806849327280293449265005 31802568497730110043474377)
        ·
          refine ⟨23851926373297582532605783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31802568497730110043474377 23851926373297582532605783)
          ·
            refine ⟨35777889559946373798908675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23851926373297582532605783 35777889559946373798908675)
            ·
              refine ⟨53666834339919560698363013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35777889559946373798908675 53666834339919560698363013)
              ·
                refine ⟨10062531438734917630943065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53666834339919560698363013 10062531438734917630943065)
                ·
                  refine ⟨7546898579051188223207299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062531438734917630943065 7546898579051188223207299)
                  ·
                    refine ⟨11320347868576782334810949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7546898579051188223207299 11320347868576782334810949)
                    ·
                      refine ⟨2122565225358146687777053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11320347868576782334810949 2122565225358146687777053)
                      ·
                        rfl

theorem cell23_4133681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4133681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133681 prefixEnd_4133681 := by exact prefixLift 4133681
  have htrace : WordTrace (prefixWord ++ tailWord_4133681) baseStart_4133681 baseEnd_4133681 := by
    simpa [prefixWord, tailWord_4133681, baseEnd_4133681] using wordTrace_append hprefix tailTrace_4133681
  have hstable : (prefixWord ++ tailWord_4133681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133681).length < 2 ^ (prefixWord ++ tailWord_4133681).sum := by decide
  have hdescent : baseEnd_4133681 < baseStart_4133681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133708 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_4133708 : Nat := 118140960795 + 4133708 * 2 ^ 59
def prefixEnd_4133708 : Nat := 4983230072969 + 3 ^ 40 * 4133708 * 2
def baseEnd_4133708 : Nat := 707526363111939360713143

theorem tailTrace_4133708 : CollatzResearch.WordTrace tailWord_4133708 prefixEnd_4133708 707526363111939360713143 := by
  unfold tailWord_4133708
  simp only [CollatzResearch.WordTrace]
  refine ⟨75384358454144685982740889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100512477938859581310321185 75384358454144685982740889)
  ·
    refine ⟨56538268840608514487055667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75384358454144685982740889 56538268840608514487055667)
    ·
      refine ⟨84807403260912771730583501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56538268840608514487055667 84807403260912771730583501)
      ·
        refine ⟨31802776222842289398968813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84807403260912771730583501 31802776222842289398968813)
        ·
          refine ⟨11926041083565858524613305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31802776222842289398968813 11926041083565858524613305)
          ·
            refine ⟨8944530812674393893459979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11926041083565858524613305 8944530812674393893459979)
            ·
              refine ⟨13416796219011590840189969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944530812674393893459979 13416796219011590840189969)
              ·
                refine ⟨10062597164258693130142477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13416796219011590840189969 10062597164258693130142477)
                ·
                  refine ⟨3773473936597009923803429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10062597164258693130142477 3773473936597009923803429)
                  ·
                    refine ⟨707526363111939360713143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773473936597009923803429 707526363111939360713143)
                    ·
                      rfl

theorem cell23_4133708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_4133708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133708 prefixEnd_4133708 := by exact prefixLift 4133708
  have htrace : WordTrace (prefixWord ++ tailWord_4133708) baseStart_4133708 baseEnd_4133708 := by
    simpa [prefixWord, tailWord_4133708, baseEnd_4133708] using wordTrace_append hprefix tailTrace_4133708
  have hstable : (prefixWord ++ tailWord_4133708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133708).length < 2 ^ (prefixWord ++ tailWord_4133708).sum := by decide
  have hdescent : baseEnd_4133708 < baseStart_4133708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133768 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_4133768 : Nat := 118140960795 + 4133768 * 2 ^ 59
def prefixEnd_4133768 : Nat := 4983230072969 + 3 ^ 40 * 4133768 * 2
def baseEnd_4133768 : Nat := 707536632725029282463051

theorem tailTrace_4133768 : CollatzResearch.WordTrace tailWord_4133768 prefixEnd_4133768 707536632725029282463051 := by
  unfold tailWord_4133768
  simp only [CollatzResearch.WordTrace]
  refine ⟨75385452644036001106332979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100513936858714668141777305 75385452644036001106332979)
  ·
    refine ⟨113078178966054001659499469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75385452644036001106332979 113078178966054001659499469)
    ·
      refine ⟨42404317112270250622312301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113078178966054001659499469 42404317112270250622312301)
      ·
        refine ⟨15901618917101343983367113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42404317112270250622312301 15901618917101343983367113)
        ·
          refine ⟨11926214187826007987525335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15901618917101343983367113 11926214187826007987525335)
          ·
            refine ⟨17889321281739011981288003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11926214187826007987525335 17889321281739011981288003)
            ·
              refine ⟨26833981922608517971932005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889321281739011981288003 26833981922608517971932005)
              ·
                refine ⟨5031371610489097119737251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26833981922608517971932005 5031371610489097119737251)
                ·
                  refine ⟨7547057415733645679605877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031371610489097119737251 7547057415733645679605877)
                  ·
                    refine ⟨707536632725029282463051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7547057415733645679605877 707536632725029282463051)
                    ·
                      rfl

theorem cell23_4133768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_4133768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133768 prefixEnd_4133768 := by exact prefixLift 4133768
  have htrace : WordTrace (prefixWord ++ tailWord_4133768) baseStart_4133768 baseEnd_4133768 := by
    simpa [prefixWord, tailWord_4133768, baseEnd_4133768] using wordTrace_append hprefix tailTrace_4133768
  have hstable : (prefixWord ++ tailWord_4133768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133768).length < 2 ^ (prefixWord ++ tailWord_4133768).sum := by decide
  have hdescent : baseEnd_4133768 < baseStart_4133768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133771 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4]
def baseStart_4133771 : Nat := 118140960795 + 4133771 * 2 ^ 59
def prefixEnd_4133771 : Nat := 4983230072969 + 3 ^ 40 * 4133771 * 2
def baseEnd_4133771 : Nat := 2122611438617051335651639

theorem tailTrace_4133771 : CollatzResearch.WordTrace tailWord_4133771 prefixEnd_4133771 2122611438617051335651639 := by
  unfold tailWord_4133771
  simp only [CollatzResearch.WordTrace]
  refine ⟨150771014707061133725025167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100514009804707422483350111 150771014707061133725025167)
  ·
    refine ⟨226156522060591700587537751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150771014707061133725025167 226156522060591700587537751)
    ·
      refine ⟨339234783090887550881306627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226156522060591700587537751 339234783090887550881306627)
      ·
        refine ⟨508852174636331326321959941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339234783090887550881306627 508852174636331326321959941)
        ·
          refine ⟨95409782744312123685367489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508852174636331326321959941 95409782744312123685367489)
          ·
            refine ⟨71557337058234092764025617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95409782744312123685367489 71557337058234092764025617)
            ·
              refine ⟨53668002793675569573019213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71557337058234092764025617 53668002793675569573019213)
              ·
                refine ⟨20125501047628338589882205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53668002793675569573019213 20125501047628338589882205)
                ·
                  refine ⟨7547062892860626971205827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20125501047628338589882205 7547062892860626971205827)
                  ·
                    refine ⟨11320594339290940456808741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547062892860626971205827 11320594339290940456808741)
                    ·
                      refine ⟨2122611438617051335651639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11320594339290940456808741 2122611438617051335651639)
                      ·
                        rfl

theorem cell23_4133771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4].length) (baseStart_4133771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133771 prefixEnd_4133771 := by exact prefixLift 4133771
  have htrace : WordTrace (prefixWord ++ tailWord_4133771) baseStart_4133771 baseEnd_4133771 := by
    simpa [prefixWord, tailWord_4133771, baseEnd_4133771] using wordTrace_append hprefix tailTrace_4133771
  have hstable : (prefixWord ++ tailWord_4133771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133771).length < 2 ^ (prefixWord ++ tailWord_4133771).sum := by decide
  have hdescent : baseEnd_4133771 < baseStart_4133771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133799 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_4133799 : Nat := 118140960795 + 4133799 * 2 ^ 59
def prefixEnd_4133799 : Nat := 4983230072969 + 3 ^ 40 * 4133799 * 2
def baseEnd_4133799 : Nat := 2122625816075377226101511

theorem tailTrace_4133799 : CollatzResearch.WordTrace tailWord_4133799 prefixEnd_4133799 2122625816075377226101511 := by
  unfold tailWord_4133799
  simp only [CollatzResearch.WordTrace]
  refine ⟨150772035950959694507044451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100514690633973129671362967 150772035950959694507044451)
  ·
    refine ⟨226158053926439541760566677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150772035950959694507044451 226158053926439541760566677)
    ·
      refine ⟨10601158777801853520026563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226158053926439541760566677 10601158777801853520026563)
      ·
        refine ⟨15901738166702780280039845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601158777801853520026563 15901738166702780280039845)
        ·
          refine ⟨2981575906256771302507471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15901738166702780280039845 2981575906256771302507471)
          ·
            refine ⟨4472363859385156953761207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981575906256771302507471 4472363859385156953761207)
            ·
              refine ⟨6708545789077735430641811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472363859385156953761207 6708545789077735430641811)
              ·
                refine ⟨10062818683616603145962717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708545789077735430641811 10062818683616603145962717)
                ·
                  refine ⟨3773557006356226179736019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10062818683616603145962717 3773557006356226179736019)
                  ·
                    refine ⟨5660335509534339269604029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773557006356226179736019 5660335509534339269604029)
                    ·
                      refine ⟨2122625816075377226101511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660335509534339269604029 2122625816075377226101511)
                      ·
                        rfl

theorem cell23_4133799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_4133799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133799 prefixEnd_4133799 := by exact prefixLift 4133799
  have htrace : WordTrace (prefixWord ++ tailWord_4133799) baseStart_4133799 baseEnd_4133799 := by
    simpa [prefixWord, tailWord_4133799, baseEnd_4133799] using wordTrace_append hprefix tailTrace_4133799
  have hstable : (prefixWord ++ tailWord_4133799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133799).length < 2 ^ (prefixWord ++ tailWord_4133799).sum := by decide
  have hdescent : baseEnd_4133799 < baseStart_4133799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133815 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 2, 4]
def baseStart_4133815 : Nat := 118140960795 + 4133815 * 2 ^ 59
def prefixEnd_4133815 : Nat := 4983230072969 + 3 ^ 40 * 4133815 * 2
def baseEnd_4133815 : Nat := 707544677255283054500479

theorem tailTrace_4133815 : CollatzResearch.WordTrace tailWord_4133815 prefixEnd_4133815 707544677255283054500479 := by
  unfold tailWord_4133815
  simp only [CollatzResearch.WordTrace]
  refine ⟨150772619518901729239626899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100515079679267819493084599 150772619518901729239626899)
  ·
    refine ⟨226158929278352593859440349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150772619518901729239626899 226158929278352593859440349)
    ·
      refine ⟨84809598479382222697290131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226158929278352593859440349 84809598479382222697290131)
      ·
        refine ⟨127214397719073334045935197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84809598479382222697290131 127214397719073334045935197)
        ·
          refine ⟨47705399144652500267225699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127214397719073334045935197 47705399144652500267225699)
          ·
            refine ⟨71558098716978750400838549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47705399144652500267225699 71558098716978750400838549)
            ·
              refine ⟨3354285877358378925039307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71558098716978750400838549 3354285877358378925039307)
              ·
                refine ⟨5031428816037568387558961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354285877358378925039307 5031428816037568387558961)
                ·
                  refine ⟨3773571612028176290669221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031428816037568387558961 3773571612028176290669221)
                  ·
                    refine ⟨707544677255283054500479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773571612028176290669221 707544677255283054500479)
                    ·
                      rfl

theorem cell23_4133815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_4133815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133815 prefixEnd_4133815 := by exact prefixLift 4133815
  have htrace : WordTrace (prefixWord ++ tailWord_4133815) baseStart_4133815 baseEnd_4133815 := by
    simpa [prefixWord, tailWord_4133815, baseEnd_4133815] using wordTrace_append hprefix tailTrace_4133815
  have hstable : (prefixWord ++ tailWord_4133815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133815).length < 2 ^ (prefixWord ++ tailWord_4133815).sum := by decide
  have hdescent : baseEnd_4133815 < baseStart_4133815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133838 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_4133838 : Nat := 118140960795 + 4133838 * 2 ^ 59
def prefixEnd_4133838 : Nat := 4983230072969 + 3 ^ 40 * 4133838 * 2
def baseEnd_4133838 : Nat := 2122645841820902573513831

theorem tailTrace_4133838 : CollatzResearch.WordTrace tailWord_4133838 prefixEnd_4133838 2122645841820902573513831 := by
  unfold tailWord_4133838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18846682299727300520964271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100515638931878936111809445 18846682299727300520964271)
  ·
    refine ⟨28270023449590950781446407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18846682299727300520964271 28270023449590950781446407)
    ·
      refine ⟨42405035174386426172169611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28270023449590950781446407 42405035174386426172169611)
      ·
        refine ⟨63607552761579639258254417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42405035174386426172169611 63607552761579639258254417)
        ·
          refine ⟨47705664571184729443690813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63607552761579639258254417 47705664571184729443690813)
          ·
            refine ⟨17889624214194273541384055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47705664571184729443690813 17889624214194273541384055)
            ·
              refine ⟨26834436321291410312076083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889624214194273541384055 26834436321291410312076083)
              ·
                refine ⟨40251654481937115468114125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26834436321291410312076083 40251654481937115468114125)
                ·
                  refine ⟨15094370430726418300542797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40251654481937115468114125 15094370430726418300542797)
                  ·
                    refine ⟨5660388911522406862703549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15094370430726418300542797 5660388911522406862703549)
                    ·
                      refine ⟨2122645841820902573513831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660388911522406862703549 2122645841820902573513831)
                      ·
                        rfl

theorem cell23_4133838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_4133838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133838 prefixEnd_4133838 := by exact prefixLift 4133838
  have htrace : WordTrace (prefixWord ++ tailWord_4133838) baseStart_4133838 baseEnd_4133838 := by
    simpa [prefixWord, tailWord_4133838, baseEnd_4133838] using wordTrace_append hprefix tailTrace_4133838
  have hstable : (prefixWord ++ tailWord_4133838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133838).length < 2 ^ (prefixWord ++ tailWord_4133838).sum := by decide
  have hdescent : baseEnd_4133838 < baseStart_4133838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133871 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 8]
def baseStart_4133871 : Nat := 118140960795 + 4133871 * 2 ^ 59
def prefixEnd_4133871 : Nat := 4983230072969 + 3 ^ 40 * 4133871 * 2
def baseEnd_4133871 : Nat := 707554262227500314800393

theorem tailTrace_4133871 : CollatzResearch.WordTrace tailWord_4133871 prefixEnd_4133871 707554262227500314800393 := by
  unfold tailWord_4133871
  simp only [CollatzResearch.WordTrace]
  refine ⟨150774662006698850803665467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100516441337799233869110311 150774662006698850803665467)
  ·
    refine ⟨226161993010048276205498201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150774662006698850803665467 226161993010048276205498201)
    ·
      refine ⟨169621494757536207154123651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226161993010048276205498201 169621494757536207154123651)
      ·
        refine ⟨254432242136304310731185477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169621494757536207154123651 254432242136304310731185477)
        ·
          refine ⟨47706045400557058262097277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254432242136304310731185477 47706045400557058262097277)
          ·
            refine ⟨17889767025208896848286479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47706045400557058262097277 17889767025208896848286479)
            ·
              refine ⟨26834650537813345272429719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889767025208896848286479 26834650537813345272429719)
              ·
                refine ⟨40251975806720017908644579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26834650537813345272429719 40251975806720017908644579)
                ·
                  refine ⟨60377963710080026862966869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40251975806720017908644579 60377963710080026862966869)
                  ·
                    refine ⟨707554262227500314800393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60377963710080026862966869 707554262227500314800393)
                    ·
                      rfl

theorem cell23_4133871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_4133871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133871 prefixEnd_4133871 := by exact prefixLift 4133871
  have htrace : WordTrace (prefixWord ++ tailWord_4133871) baseStart_4133871 baseEnd_4133871 := by
    simpa [prefixWord, tailWord_4133871, baseEnd_4133871] using wordTrace_append hprefix tailTrace_4133871
  have hstable : (prefixWord ++ tailWord_4133871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133871).length < 2 ^ (prefixWord ++ tailWord_4133871).sum := by decide
  have hdescent : baseEnd_4133871 < baseStart_4133871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133895 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_4133895 : Nat := 118140960795 + 4133895 * 2 ^ 59
def prefixEnd_4133895 : Nat := 4983230072969 + 3 ^ 40 * 4133895 * 2
def baseEnd_4133895 : Nat := 2122675110218208850501069

theorem tailTrace_4133895 : CollatzResearch.WordTrace tailWord_4133895 prefixEnd_4133895 2122675110218208850501069 := by
  unfold tailWord_4133895
  simp only [CollatzResearch.WordTrace]
  refine ⟨150775537358611902902539139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100517024905741268601692759 150775537358611902902539139)
  ·
    refine ⟨226163306037917854353808709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150775537358611902902539139 226163306037917854353808709)
    ·
      refine ⟨42405619882109597691339133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226163306037917854353808709 42405619882109597691339133)
      ·
        refine ⟨15902107455791099134252175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42405619882109597691339133 15902107455791099134252175)
        ·
          refine ⟨23853161183686648701378263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15902107455791099134252175 23853161183686648701378263)
          ·
            refine ⟨35779741775529973052067395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23853161183686648701378263 35779741775529973052067395)
            ·
              refine ⟨53669612663294959578101093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35779741775529973052067395 53669612663294959578101093)
              ·
                refine ⟨10063052374367804920893955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53669612663294959578101093 10063052374367804920893955)
                ·
                  refine ⟨15094578561551707381340933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10063052374367804920893955 15094578561551707381340933)
                  ·
                    refine ⟨2830233480290945134001425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15094578561551707381340933 2830233480290945134001425)
                    ·
                      refine ⟨2122675110218208850501069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830233480290945134001425 2122675110218208850501069)
                      ·
                        rfl

theorem cell23_4133895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_4133895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133895 prefixEnd_4133895 := by exact prefixLift 4133895
  have htrace : WordTrace (prefixWord ++ tailWord_4133895) baseStart_4133895 baseEnd_4133895 := by
    simpa [prefixWord, tailWord_4133895, baseEnd_4133895] using wordTrace_append hprefix tailTrace_4133895
  have hstable : (prefixWord ++ tailWord_4133895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133895).length < 2 ^ (prefixWord ++ tailWord_4133895).sum := by decide
  have hdescent : baseEnd_4133895 < baseStart_4133895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133899 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 1, 3, 2]
def baseStart_4133899 : Nat := 118140960795 + 4133899 * 2 ^ 59
def prefixEnd_4133899 : Nat := 4983230072969 + 3 ^ 40 * 4133899 * 2
def baseEnd_4133899 : Nat := 2122677164140826834851051

theorem tailTrace_4133899 : CollatzResearch.WordTrace tailWord_4133899 prefixEnd_4133899 2122677164140826834851051 := by
  unfold tailWord_4133899
  simp only [CollatzResearch.WordTrace]
  refine ⟨150775683250597411585684751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100517122167064941057123167 150775683250597411585684751)
  ·
    refine ⟨226163524875896117378527127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150775683250597411585684751 226163524875896117378527127)
    ·
      refine ⟨339245287313844176067790691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226163524875896117378527127 339245287313844176067790691)
      ·
        refine ⟨508867930970766264101686037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339245287313844176067790691 508867930970766264101686037)
        ·
          refine ⟨23853184264254668629766533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 508867930970766264101686037 23853184264254668629766533)
          ·
            refine ⟨4472472049547750368081225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23853184264254668629766533 4472472049547750368081225)
            ·
              refine ⟨3354354037160812776060919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472472049547750368081225 3354354037160812776060919)
              ·
                refine ⟨5031531055741219164091379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354354037160812776060919 5031531055741219164091379)
                ·
                  refine ⟨7547296583611828746137069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031531055741219164091379 7547296583611828746137069)
                  ·
                    refine ⟨2830236218854435779801401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7547296583611828746137069 2830236218854435779801401)
                    ·
                      refine ⟨2122677164140826834851051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830236218854435779801401 2122677164140826834851051)
                      ·
                        rfl

theorem cell23_4133899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 3, 2].length) (baseStart_4133899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133899 prefixEnd_4133899 := by exact prefixLift 4133899
  have htrace : WordTrace (prefixWord ++ tailWord_4133899) baseStart_4133899 baseEnd_4133899 := by
    simpa [prefixWord, tailWord_4133899, baseEnd_4133899] using wordTrace_append hprefix tailTrace_4133899
  have hstable : (prefixWord ++ tailWord_4133899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133899).length < 2 ^ (prefixWord ++ tailWord_4133899).sum := by decide
  have hdescent : baseEnd_4133899 < baseStart_4133899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133906 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4133906 : Nat := 118140960795 + 4133906 * 2 ^ 59
def prefixEnd_4133906 : Nat := 4983230072969 + 3 ^ 40 * 4133906 * 2
def baseEnd_4133906 : Nat := 2122680758505408307463519

theorem tailTrace_4133906 : CollatzResearch.WordTrace tailWord_4133906 prefixEnd_4133906 2122680758505408307463519 := by
  unfold tailWord_4133906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37693984640393012945297393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100517292374381367854126381 37693984640393012945297393)
  ·
    refine ⟨28270488480294759708973045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37693984640393012945297393 28270488480294759708973045)
    ·
      refine ⟨2650358295027633722716223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28270488480294759708973045 2650358295027633722716223)
      ·
        refine ⟨3975537442541450584074335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650358295027633722716223 3975537442541450584074335)
        ·
          refine ⟨5963306163812175876111503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975537442541450584074335 5963306163812175876111503)
          ·
            refine ⟨8944959245718263814167255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963306163812175876111503 8944959245718263814167255)
            ·
              refine ⟨13417438868577395721250883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944959245718263814167255 13417438868577395721250883)
              ·
                refine ⟨20126158302866093581876325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13417438868577395721250883 20126158302866093581876325)
                ·
                  refine ⟨3773654681787392546601811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20126158302866093581876325 3773654681787392546601811)
                  ·
                    refine ⟨5660482022681088819902717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773654681787392546601811 5660482022681088819902717)
                    ·
                      refine ⟨2122680758505408307463519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660482022681088819902717 2122680758505408307463519)
                      ·
                        rfl

theorem cell23_4133906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4133906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133906 prefixEnd_4133906 := by exact prefixLift 4133906
  have htrace : WordTrace (prefixWord ++ tailWord_4133906) baseStart_4133906 baseEnd_4133906 := by
    simpa [prefixWord, tailWord_4133906, baseEnd_4133906] using wordTrace_append hprefix tailTrace_4133906
  have hstable : (prefixWord ++ tailWord_4133906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133906).length < 2 ^ (prefixWord ++ tailWord_4133906).sum := by decide
  have hdescent : baseEnd_4133906 < baseStart_4133906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133912 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4133912 : Nat := 118140960795 + 4133912 * 2 ^ 59
def prefixEnd_4133912 : Nat := 4983230072969 + 3 ^ 40 * 4133912 * 2
def baseEnd_4133912 : Nat := 2122683839389335283988491

theorem tailTrace_4133912 : CollatzResearch.WordTrace tailWord_4133912 prefixEnd_4133912 2122683839389335283988491 := by
  unfold tailWord_4133912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75388078699775157402953995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100517438266366876537271993 75388078699775157402953995)
  ·
    refine ⟨113082118049662736104430993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75388078699775157402953995 113082118049662736104430993)
    ·
      refine ⟨84811588537247052078323245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113082118049662736104430993 84811588537247052078323245)
      ·
        refine ⟨31804345701467644529371217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84811588537247052078323245 31804345701467644529371217)
        ·
          refine ⟨23853259276100733397028413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31804345701467644529371217 23853259276100733397028413)
          ·
            refine ⟨8944972228537775023885655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23853259276100733397028413 8944972228537775023885655)
            ·
              refine ⟨13417458342806662535828483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944972228537775023885655 13417458342806662535828483)
              ·
                refine ⟨20126187514209993803742725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13417458342806662535828483 20126187514209993803742725)
                ·
                  refine ⟨3773660158914373838201761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20126187514209993803742725 3773660158914373838201761)
                  ·
                    refine ⟨2830245119185780378651321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3773660158914373838201761 2830245119185780378651321)
                    ·
                      refine ⟨2122683839389335283988491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830245119185780378651321 2122683839389335283988491)
                      ·
                        rfl

theorem cell23_4133912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4133912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133912 prefixEnd_4133912 := by exact prefixLift 4133912
  have htrace : WordTrace (prefixWord ++ tailWord_4133912) baseStart_4133912 baseEnd_4133912 := by
    simpa [prefixWord, tailWord_4133912, baseEnd_4133912] using wordTrace_append hprefix tailTrace_4133912
  have hstable : (prefixWord ++ tailWord_4133912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133912).length < 2 ^ (prefixWord ++ tailWord_4133912).sum := by decide
  have hdescent : baseEnd_4133912 < baseStart_4133912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133931 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 7]
def baseStart_4133931 : Nat := 118140960795 + 4133931 * 2 ^ 59
def prefixEnd_4133931 : Nat := 4983230072969 + 3 ^ 40 * 4133931 * 2
def baseEnd_4133931 : Nat := 707564531840590236550301

theorem tailTrace_4133931 : CollatzResearch.WordTrace tailWord_4133931 prefixEnd_4133931 707564531840590236550301 := by
  unfold tailWord_4133931
  simp only [CollatzResearch.WordTrace]
  refine ⟨150776850386481481050849647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100517900257654320700566431 150776850386481481050849647)
  ·
    refine ⟨226165275579722221576274471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150776850386481481050849647 226165275579722221576274471)
    ·
      refine ⟨339247913369583332364411707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226165275579722221576274471 339247913369583332364411707)
      ·
        refine ⟨508871870054374998546617561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339247913369583332364411707 508871870054374998546617561)
        ·
          refine ⟨381653902540781248909963171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508871870054374998546617561 381653902540781248909963171)
          ·
            refine ⟨572480853811171873364944757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381653902540781248909963171 572480853811171873364944757)
            ·
              refine ⟨53670080044797363127963571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 572480853811171873364944757 53670080044797363127963571)
              ·
                refine ⟨80505120067196044691945357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53670080044797363127963571 80505120067196044691945357)
                ·
                  refine ⟨30189420025198516759479509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80505120067196044691945357 30189420025198516759479509)
                  ·
                    refine ⟨707564531840590236550301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30189420025198516759479509 707564531840590236550301)
                    ·
                      rfl

theorem cell23_4133931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_4133931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133931 prefixEnd_4133931 := by exact prefixLift 4133931
  have htrace : WordTrace (prefixWord ++ tailWord_4133931) baseStart_4133931 baseEnd_4133931 := by
    simpa [prefixWord, tailWord_4133931, baseEnd_4133931] using wordTrace_append hprefix tailTrace_4133931
  have hstable : (prefixWord ++ tailWord_4133931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133931).length < 2 ^ (prefixWord ++ tailWord_4133931).sum := by decide
  have hdescent : baseEnd_4133931 < baseStart_4133931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133948 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_4133948 : Nat := 118140960795 + 4133948 * 2 ^ 59
def prefixEnd_4133948 : Nat := 4983230072969 + 3 ^ 40 * 4133948 * 2
def baseEnd_4133948 : Nat := 707567441564299047712775

theorem tailTrace_4133948 : CollatzResearch.WordTrace tailWord_4133948 prefixEnd_4133948 707567441564299047712775 := by
  unfold tailWord_4133948
  simp only [CollatzResearch.WordTrace]
  refine ⟨75388735213709946477109249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100518313618279928636145665 75388735213709946477109249)
  ·
    refine ⟨56541551410282459857831937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75388735213709946477109249 56541551410282459857831937)
    ·
      refine ⟨42406163557711844893373953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56541551410282459857831937 42406163557711844893373953)
      ·
        refine ⟨31804622668283883670030465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42406163557711844893373953 31804622668283883670030465)
        ·
          refine ⟨23853467001212912752522849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31804622668283883670030465 23853467001212912752522849)
          ·
            refine ⟨17890100250909684564392137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23853467001212912752522849 17890100250909684564392137)
            ·
              refine ⟨13417575188182263423294103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17890100250909684564392137 13417575188182263423294103)
              ·
                refine ⟨20126362782273395134941155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13417575188182263423294103 20126362782273395134941155)
                ·
                  refine ⟨30189544173410092702411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20126362782273395134941155 30189544173410092702411733)
                  ·
                    refine ⟨707567441564299047712775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30189544173410092702411733 707567441564299047712775)
                    ·
                      rfl

theorem cell23_4133948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_4133948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133948 prefixEnd_4133948 := by exact prefixLift 4133948
  have htrace : WordTrace (prefixWord ++ tailWord_4133948) baseStart_4133948 baseEnd_4133948 := by
    simpa [prefixWord, tailWord_4133948, baseEnd_4133948] using wordTrace_append hprefix tailTrace_4133948
  have hstable : (prefixWord ++ tailWord_4133948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133948).length < 2 ^ (prefixWord ++ tailWord_4133948).sum := by decide
  have hdescent : baseEnd_4133948 < baseStart_4133948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133965 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4133965 : Nat := 118140960795 + 4133965 * 2 ^ 59
def prefixEnd_4133965 : Nat := 4983230072969 + 3 ^ 40 * 4133965 * 2
def baseEnd_4133965 : Nat := 707570351288007858875249

theorem tailTrace_4133965 : CollatzResearch.WordTrace tailWord_4133965 prefixEnd_4133965 707570351288007858875249 := by
  unfold tailWord_4133965
  simp only [CollatzResearch.WordTrace]
  refine ⟨150778090468358304857587349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100518726978905536571724899 150778090468358304857587349)
  ·
    refine ⟨7067722990704295540199407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150778090468358304857587349 7067722990704295540199407)
    ·
      refine ⟨10601584486056443310299111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067722990704295540199407 10601584486056443310299111)
      ·
        refine ⟨15902376729084664965448667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601584486056443310299111 15902376729084664965448667)
        ·
          refine ⟨23853565093626997448173001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15902376729084664965448667 23853565093626997448173001)
          ·
            refine ⟨17890173820220248086129751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23853565093626997448173001 17890173820220248086129751)
            ·
              refine ⟨26835260730330372129194627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17890173820220248086129751 26835260730330372129194627)
              ·
                refine ⟨40252891095495558193791941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26835260730330372129194627 40252891095495558193791941)
                ·
                  refine ⟨7547417080405417161335989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40252891095495558193791941 7547417080405417161335989)
                  ·
                    refine ⟨707570351288007858875249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7547417080405417161335989 707570351288007858875249)
                    ·
                      rfl

theorem cell23_4133965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4133965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133965 prefixEnd_4133965 := by exact prefixLift 4133965
  have htrace : WordTrace (prefixWord ++ tailWord_4133965) baseStart_4133965 baseEnd_4133965 := by
    simpa [prefixWord, tailWord_4133965, baseEnd_4133965] using wordTrace_append hprefix tailTrace_4133965
  have hstable : (prefixWord ++ tailWord_4133965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133965).length < 2 ^ (prefixWord ++ tailWord_4133965).sum := by decide
  have hdescent : baseEnd_4133965 < baseStart_4133965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133985 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_4133985 : Nat := 118140960795 + 4133985 * 2 ^ 59
def prefixEnd_4133985 : Nat := 4983230072969 + 3 ^ 40 * 4133985 * 2
def baseEnd_4133985 : Nat := 2122721323477113498375655

theorem tailTrace_4133985 : CollatzResearch.WordTrace tailWord_4133985 prefixEnd_4133985 2122721323477113498375655 := by
  unfold tailWord_4133985
  simp only [CollatzResearch.WordTrace]
  refine ⟨150778819928285848273315409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100519213285523898848876939 150778819928285848273315409)
  ·
    refine ⟨113084114946214386204986557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150778819928285848273315409 113084114946214386204986557)
    ·
      refine ⟨42406543104830394826869959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113084114946214386204986557 42406543104830394826869959)
      ·
        refine ⟨63609814657245592240304939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42406543104830394826869959 63609814657245592240304939)
        ·
          refine ⟨95414721985868388360457409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63609814657245592240304939 95414721985868388360457409)
          ·
            refine ⟨71561041489401291270343057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95414721985868388360457409 71561041489401291270343057)
            ·
              refine ⟨53670781117050968452757293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71561041489401291270343057 53670781117050968452757293)
              ·
                refine ⟨20126542918894113169783985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53670781117050968452757293 20126542918894113169783985)
                ·
                  refine ⟨15094907189170584877337989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20126542918894113169783985 15094907189170584877337989)
                  ·
                    refine ⟨2830295097969484664500873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15094907189170584877337989 2830295097969484664500873)
                    ·
                      refine ⟨2122721323477113498375655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830295097969484664500873 2122721323477113498375655)
                      ·
                        rfl

theorem cell23_4133985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_4133985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4133985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4133985 prefixEnd_4133985 := by exact prefixLift 4133985
  have htrace : WordTrace (prefixWord ++ tailWord_4133985) baseStart_4133985 baseEnd_4133985 := by
    simpa [prefixWord, tailWord_4133985, baseEnd_4133985] using wordTrace_append hprefix tailTrace_4133985
  have hstable : (prefixWord ++ tailWord_4133985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133985).length < 2 ^ (prefixWord ++ tailWord_4133985).sum := by decide
  have hdescent : baseEnd_4133985 < baseStart_4133985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134012 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_4134012 : Nat := 118140960795 + 4134012 * 2 ^ 59
def prefixEnd_4134012 : Nat := 4983230072969 + 3 ^ 40 * 4134012 * 2
def baseEnd_4134012 : Nat := 707578395818261630912677

theorem tailTrace_4134012 : CollatzResearch.WordTrace tailWord_4134012 prefixEnd_4134012 707578395818261630912677 := by
  unfold tailWord_4134012
  simp only [CollatzResearch.WordTrace]
  refine ⟨75389902349594015942274145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100519869799458687923032193 75389902349594015942274145)
  ·
    refine ⟨56542426762195511956705609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75389902349594015942274145 56542426762195511956705609)
    ·
      refine ⟨42406820071646633967529207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56542426762195511956705609 42406820071646633967529207)
      ·
        refine ⟨63610230107469950951293811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42406820071646633967529207 63610230107469950951293811)
        ·
          refine ⟨95415345161204926426940717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63610230107469950951293811 95415345161204926426940717)
          ·
            refine ⟨35780754435451847410102769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95415345161204926426940717 35780754435451847410102769)
            ·
              refine ⟨26835565826588885557577077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35780754435451847410102769 26835565826588885557577077)
              ·
                refine ⟨2515834296242708021022851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26835565826588885557577077 2515834296242708021022851)
                ·
                  refine ⟨3773751444364062031534277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515834296242708021022851 3773751444364062031534277)
                  ·
                    refine ⟨707578395818261630912677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773751444364062031534277 707578395818261630912677)
                    ·
                      rfl

theorem cell23_4134012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_4134012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134012 prefixEnd_4134012 := by exact prefixLift 4134012
  have htrace : WordTrace (prefixWord ++ tailWord_4134012) baseStart_4134012 baseEnd_4134012 := by
    simpa [prefixWord, tailWord_4134012, baseEnd_4134012] using wordTrace_append hprefix tailTrace_4134012
  have hstable : (prefixWord ++ tailWord_4134012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134012).length < 2 ^ (prefixWord ++ tailWord_4134012).sum := by decide
  have hdescent : baseEnd_4134012 < baseStart_4134012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134025 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 6]
def baseStart_4134025 : Nat := 118140960795 + 4134025 * 2 ^ 59
def prefixEnd_4134025 : Nat := 4983230072969 + 3 ^ 40 * 4134025 * 2
def baseEnd_4134025 : Nat := 235860206967032593541719

theorem tailTrace_4134025 : CollatzResearch.WordTrace tailWord_4134025 prefixEnd_4134025 235860206967032593541719 := by
  unfold tailWord_4134025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150780278848140935104771529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100520185898760623403181019 150780278848140935104771529)
  ·
    refine ⟨113085209136105701328578647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150780278848140935104771529 113085209136105701328578647)
    ·
      refine ⟨169627813704158551992867971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113085209136105701328578647 169627813704158551992867971)
      ·
        refine ⟨254441720556237827989301957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169627813704158551992867971 254441720556237827989301957)
        ·
          refine ⟨47707822604294592747994117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254441720556237827989301957 47707822604294592747994117)
          ·
            refine ⟨8945216738305236140248897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47707822604294592747994117 8945216738305236140248897)
            ·
              refine ⟨6708912553728927105186673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8945216738305236140248897 6708912553728927105186673)
              ·
                refine ⟨5031684415296695328890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6708912553728927105186673 5031684415296695328890005)
                ·
                  refine ⟨235860206967032593541719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5031684415296695328890005 235860206967032593541719)
                  ·
                    rfl

theorem cell23_4134025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_4134025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134025 prefixEnd_4134025 := by exact prefixLift 4134025
  have htrace : WordTrace (prefixWord ++ tailWord_4134025) baseStart_4134025 baseEnd_4134025 := by
    simpa [prefixWord, tailWord_4134025, baseEnd_4134025] using wordTrace_append hprefix tailTrace_4134025
  have hstable : (prefixWord ++ tailWord_4134025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134025).length < 2 ^ (prefixWord ++ tailWord_4134025).sum := by decide
  have hdescent : baseEnd_4134025 < baseStart_4134025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134048 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4134048 : Nat := 118140960795 + 4134048 * 2 ^ 59
def prefixEnd_4134048 : Nat := 4983230072969 + 3 ^ 40 * 4134048 * 2
def baseEnd_4134048 : Nat := 2122753672758346751887865

theorem tailTrace_4134048 : CollatzResearch.WordTrace tailWord_4134048 prefixEnd_4134048 2122753672758346751887865 := by
  unfold tailWord_4134048
  simp only [CollatzResearch.WordTrace]
  refine ⟨75390558863528805016429399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100520745151371740021905865 75390558863528805016429399)
  ·
    refine ⟨113085838295293207524644099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75390558863528805016429399 113085838295293207524644099)
    ·
      refine ⟨169628757442939811286966149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113085838295293207524644099 169628757442939811286966149)
      ·
        refine ⟨31805392020551214616306153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169628757442939811286966149 31805392020551214616306153)
        ·
          refine ⟨23854044015413410962229615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31805392020551214616306153 23854044015413410962229615)
          ·
            refine ⟨35781066023120116443344423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23854044015413410962229615 35781066023120116443344423)
            ·
              refine ⟨53671599034680174665016635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35781066023120116443344423 53671599034680174665016635)
              ·
                refine ⟨80507398552020261997524953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53671599034680174665016635 80507398552020261997524953)
                ·
                  refine ⟨60380548914015196498143715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80507398552020261997524953 60380548914015196498143715)
                  ·
                    refine ⟨90570823371022794747215573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60380548914015196498143715 90570823371022794747215573)
                    ·
                      refine ⟨2122753672758346751887865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90570823371022794747215573 2122753672758346751887865)
                      ·
                        rfl

theorem cell23_4134048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4134048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134048 prefixEnd_4134048 := by exact prefixLift 4134048
  have htrace : WordTrace (prefixWord ++ tailWord_4134048) baseStart_4134048 baseEnd_4134048 := by
    simpa [prefixWord, tailWord_4134048, baseEnd_4134048] using wordTrace_append hprefix tailTrace_4134048
  have hstable : (prefixWord ++ tailWord_4134048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134048).length < 2 ^ (prefixWord ++ tailWord_4134048).sum := by decide
  have hdescent : baseEnd_4134048 < baseStart_4134048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134052 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_4134052 : Nat := 118140960795 + 4134052 * 2 ^ 59
def prefixEnd_4134052 : Nat := 4983230072969 + 3 ^ 40 * 4134052 * 2
def baseEnd_4134052 : Nat := 2122755726680964736237847

theorem tailTrace_4134052 : CollatzResearch.WordTrace tailWord_4134052 prefixEnd_4134052 2122755726680964736237847 := by
  unfold tailWord_4134052
  simp only [CollatzResearch.WordTrace]
  refine ⟨75390631809521559358002205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100520842412695412477336273 75390631809521559358002205)
  ·
    refine ⟨28271486928570584759250827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75390631809521559358002205 28271486928570584759250827)
    ·
      refine ⟨42407230392855877138876241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28271486928570584759250827 42407230392855877138876241)
      ·
        refine ⟨31805422794641907854157181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42407230392855877138876241 31805422794641907854157181)
        ·
          refine ⟨11927033547990715445308943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31805422794641907854157181 11927033547990715445308943)
          ·
            refine ⟨17890550321986073167963415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927033547990715445308943 17890550321986073167963415)
            ·
              refine ⟨26835825482979109751945123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17890550321986073167963415 26835825482979109751945123)
              ·
                refine ⟨40253738224468664627917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26835825482979109751945123 40253738224468664627917685)
                ·
                  refine ⟨3773787958543937308867283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40253738224468664627917685 3773787958543937308867283)
                  ·
                    refine ⟨5660681937815905963300925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773787958543937308867283 5660681937815905963300925)
                    ·
                      refine ⟨2122755726680964736237847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660681937815905963300925 2122755726680964736237847)
                      ·
                        rfl

theorem cell23_4134052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_4134052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134052 prefixEnd_4134052 := by exact prefixLift 4134052
  have htrace : WordTrace (prefixWord ++ tailWord_4134052) baseStart_4134052 baseEnd_4134052 := by
    simpa [prefixWord, tailWord_4134052, baseEnd_4134052] using wordTrace_append hprefix tailTrace_4134052
  have hstable : (prefixWord ++ tailWord_4134052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134052).length < 2 ^ (prefixWord ++ tailWord_4134052).sum := by decide
  have hdescent : baseEnd_4134052 < baseStart_4134052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134095 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_4134095 : Nat := 118140960795 + 4134095 * 2 ^ 59
def prefixEnd_4134095 : Nat := 4983230072969 + 3 ^ 40 * 4134095 * 2
def baseEnd_4134095 : Nat := 2122777806349108068000149

theorem tailTrace_4134095 : CollatzResearch.WordTrace tailWord_4134095 prefixEnd_4134095 2122777806349108068000149 := by
  unfold tailWord_4134095
  simp only [CollatzResearch.WordTrace]
  refine ⟨150782831957887337059819739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100521887971924891373213159 150782831957887337059819739)
  ·
    refine ⟨226174247936831005589729609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150782831957887337059819739 226174247936831005589729609)
    ·
      refine ⟨169630685952623254192297207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226174247936831005589729609 169630685952623254192297207)
      ·
        refine ⟨254446028928934881288445811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169630685952623254192297207 254446028928934881288445811)
        ·
          refine ⟨381669043393402321932668717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254446028928934881288445811 381669043393402321932668717)
          ·
            refine ⟨143125891272525870724750769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381669043393402321932668717 143125891272525870724750769)
            ·
              refine ⟨107344418454394403043563077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143125891272525870724750769 107344418454394403043563077)
              ·
                refine ⟨20127078460198950570668077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107344418454394403043563077 20127078460198950570668077)
                ·
                  refine ⟨7547654422574606464000529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20127078460198950570668077 7547654422574606464000529)
                  ·
                    refine ⟨5660740816930954848000397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7547654422574606464000529 5660740816930954848000397)
                    ·
                      refine ⟨2122777806349108068000149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660740816930954848000397 2122777806349108068000149)
                      ·
                        rfl

theorem cell23_4134095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_4134095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134095 prefixEnd_4134095 := by exact prefixLift 4134095
  have htrace : WordTrace (prefixWord ++ tailWord_4134095) baseStart_4134095 baseEnd_4134095 := by
    simpa [prefixWord, tailWord_4134095, baseEnd_4134095] using wordTrace_append hprefix tailTrace_4134095
  have hstable : (prefixWord ++ tailWord_4134095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134095).length < 2 ^ (prefixWord ++ tailWord_4134095).sum := by decide
  have hdescent : baseEnd_4134095 < baseStart_4134095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134112 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_4134112 : Nat := 118140960795 + 4134112 * 2 ^ 59
def prefixEnd_4134112 : Nat := 4983230072969 + 3 ^ 40 * 4134112 * 2
def baseEnd_4134112 : Nat := 2122786535520234501487571

theorem tailTrace_4134112 : CollatzResearch.WordTrace tailWord_4134112 prefixEnd_4134112 2122786535520234501487571 := by
  unfold tailWord_4134112
  simp only [CollatzResearch.WordTrace]
  refine ⟨75391725999412874481594295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100522301332550499308792393 75391725999412874481594295)
  ·
    refine ⟨113087588999119311722391443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75391725999412874481594295 113087588999119311722391443)
    ·
      refine ⟨169631383498678967583587165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113087588999119311722391443 169631383498678967583587165)
      ·
        refine ⟨63611768812004612843845187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169631383498678967583587165 63611768812004612843845187)
        ·
          refine ⟨95417653218006919265767781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63611768812004612843845187 95417653218006919265767781)
          ·
            refine ⟨17890809978376297362331459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95417653218006919265767781 17890809978376297362331459)
            ·
              refine ⟨26836214967564446043497189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17890809978376297362331459 26836214967564446043497189)
              ·
                refine ⟨5031790306418333633155723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26836214967564446043497189 5031790306418333633155723)
                ·
                  refine ⟨7547685459627500449733585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031790306418333633155723 7547685459627500449733585)
                  ·
                    refine ⟨5660764094720625337300189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7547685459627500449733585 5660764094720625337300189)
                    ·
                      refine ⟨2122786535520234501487571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5660764094720625337300189 2122786535520234501487571)
                      ·
                        rfl

theorem cell23_4134112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_4134112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134112 prefixEnd_4134112 := by exact prefixLift 4134112
  have htrace : WordTrace (prefixWord ++ tailWord_4134112) baseStart_4134112 baseEnd_4134112 := by
    simpa [prefixWord, tailWord_4134112, baseEnd_4134112] using wordTrace_append hprefix tailTrace_4134112
  have hstable : (prefixWord ++ tailWord_4134112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134112).length < 2 ^ (prefixWord ++ tailWord_4134112).sum := by decide
  have hdescent : baseEnd_4134112 < baseStart_4134112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134128 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_4134128 : Nat := 118140960795 + 4134128 * 2 ^ 59
def prefixEnd_4134128 : Nat := 4983230072969 + 3 ^ 40 * 4134128 * 2
def baseEnd_4134128 : Nat := 707598250403568812962499

theorem tailTrace_4134128 : CollatzResearch.WordTrace tailWord_4134128 prefixEnd_4134128 707598250403568812962499 := by
  unfold tailWord_4134128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75392017783383891847885519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100522690377845189130514025 75392017783383891847885519)
  ·
    refine ⟨113088026675075837771828279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75392017783383891847885519 113088026675075837771828279)
    ·
      refine ⟨169632040012613756657742419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113088026675075837771828279 169632040012613756657742419)
      ·
        refine ⟨254448060018920634986613629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169632040012613756657742419 254448060018920634986613629)
        ·
          refine ⟨95418022507095238119980111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254448060018920634986613629 95418022507095238119980111)
          ·
            refine ⟨143127033760642857179970167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95418022507095238119980111 143127033760642857179970167)
            ·
              refine ⟨214690550640964285769955251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143127033760642857179970167 214690550640964285769955251)
              ·
                refine ⟨322035825961446428654932877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214690550640964285769955251 322035825961446428654932877)
                ·
                  refine ⟨120763434735542410745599829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322035825961446428654932877 120763434735542410745599829)
                  ·
                    refine ⟨707598250403568812962499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 120763434735542410745599829 707598250403568812962499)
                    ·
                      rfl

theorem cell23_4134128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_4134128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134128 prefixEnd_4134128 := by exact prefixLift 4134128
  have htrace : WordTrace (prefixWord ++ tailWord_4134128) baseStart_4134128 baseEnd_4134128 := by
    simpa [prefixWord, tailWord_4134128, baseEnd_4134128] using wordTrace_append hprefix tailTrace_4134128
  have hstable : (prefixWord ++ tailWord_4134128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134128).length < 2 ^ (prefixWord ++ tailWord_4134128).sum := by decide
  have hdescent : baseEnd_4134128 < baseStart_4134128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134143 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 1, 2, 2]
def baseStart_4134143 : Nat := 118140960795 + 4134143 * 2 ^ 59
def prefixEnd_4134143 : Nat := 4983230072969 + 3 ^ 40 * 4134143 * 2
def baseEnd_4134143 : Nat := 2122802453420523880199929

theorem tailTrace_4134143 : CollatzResearch.WordTrace tailWord_4134143 prefixEnd_4134143 2122802453420523880199929 := by
  unfold tailWord_4134143
  simp only [CollatzResearch.WordTrace]
  refine ⟨150784582661713441257567083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100523055107808960838378055 150784582661713441257567083)
  ·
    refine ⟨226176873992570161886350625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150784582661713441257567083 226176873992570161886350625)
    ·
      refine ⟨169632655494427621414762969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226176873992570161886350625 169632655494427621414762969)
      ·
        refine ⟨127224491620820716061072227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169632655494427621414762969 127224491620820716061072227)
        ·
          refine ⟨190836737431231074091608341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127224491620820716061072227 190836737431231074091608341)
          ·
            refine ⟨8945472067088956598044141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190836737431231074091608341 8945472067088956598044141)
            ·
              refine ⟨3354552025158358724266553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8945472067088956598044141 3354552025158358724266553)
              ·
                refine ⟨2515914018868769043199915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354552025158358724266553 2515914018868769043199915)
                ·
                  refine ⟨3773871028303153564799873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515914018868769043199915 3773871028303153564799873)
                  ·
                    refine ⟨2830403271227365173599905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3773871028303153564799873 2830403271227365173599905)
                    ·
                      refine ⟨2122802453420523880199929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830403271227365173599905 2122802453420523880199929)
                      ·
                        rfl

theorem cell23_4134143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_4134143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134143 prefixEnd_4134143 := by exact prefixLift 4134143
  have htrace : WordTrace (prefixWord ++ tailWord_4134143) baseStart_4134143 baseEnd_4134143 := by
    simpa [prefixWord, tailWord_4134143, baseEnd_4134143] using wordTrace_append hprefix tailTrace_4134143
  have hstable : (prefixWord ++ tailWord_4134143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134143).length < 2 ^ (prefixWord ++ tailWord_4134143).sum := by decide
  have hdescent : baseEnd_4134143 < baseStart_4134143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134250 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4134250 : Nat := 118140960795 + 4134250 * 2 ^ 59
def prefixEnd_4134250 : Nat := 4983230072969 + 3 ^ 40 * 4134250 * 2
def baseEnd_4134250 : Nat := 2122857395850554961561937

theorem tailTrace_4134250 : CollatzResearch.WordTrace tailWord_4134250 prefixEnd_4134250 2122857395850554961561937 := by
  unfold tailWord_4134250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697121318081449632928051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100525656848217199021141469 37697121318081449632928051)
  ·
    refine ⟨56545681977122174449392077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37697121318081449632928051 56545681977122174449392077)
    ·
      refine ⟨21204630741420815418522029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56545681977122174449392077 21204630741420815418522029)
      ·
        refine ⟨7951736528032805781945761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21204630741420815418522029 7951736528032805781945761)
        ·
          refine ⟨5963802396024604336459321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7951736528032805781945761 5963802396024604336459321)
          ·
            refine ⟨4472851797018453252344491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5963802396024604336459321 4472851797018453252344491)
            ·
              refine ⟨6709277695527679878516737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472851797018453252344491 6709277695527679878516737)
              ·
                refine ⟨5031958271645759908887553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6709277695527679878516737 5031958271645759908887553)
                ·
                  refine ⟨3773968703734319931665665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031958271645759908887553 3773968703734319931665665)
                  ·
                    refine ⟨2830476527800739948749249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3773968703734319931665665 2830476527800739948749249)
                    ·
                      refine ⟨2122857395850554961561937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830476527800739948749249 2122857395850554961561937)
                      ·
                        rfl

theorem cell23_4134250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4134250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134250 prefixEnd_4134250 := by exact prefixLift 4134250
  have htrace : WordTrace (prefixWord ++ tailWord_4134250) baseStart_4134250 baseEnd_4134250 := by
    simpa [prefixWord, tailWord_4134250, baseEnd_4134250] using wordTrace_append hprefix tailTrace_4134250
  have hstable : (prefixWord ++ tailWord_4134250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134250).length < 2 ^ (prefixWord ++ tailWord_4134250).sum := by decide
  have hdescent : baseEnd_4134250 < baseStart_4134250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134290 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_4134290 : Nat := 118140960795 + 4134290 * 2 ^ 59
def prefixEnd_4134290 : Nat := 4983230072969 + 3 ^ 40 * 4134290 * 2
def baseEnd_4134290 : Nat := 235875326119637200562417

theorem tailTrace_4134290 : CollatzResearch.WordTrace tailWord_4134290 prefixEnd_4134290 235875326119637200562417 := by
  unfold tailWord_4134290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697486048045221340792081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100526629461453923575445549 37697486048045221340792081)
  ·
    refine ⟨28273114536033916005594061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37697486048045221340792081 28273114536033916005594061)
    ·
      refine ⟨10602417951012718502097773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28273114536033916005594061 10602417951012718502097773)
      ·
        refine ⟨3975906731629769438286665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10602417951012718502097773 3975906731629769438286665)
        ·
          refine ⟨2981930048722327078714999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3975906731629769438286665 2981930048722327078714999)
          ·
            refine ⟨4472895073083490618072499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981930048722327078714999 4472895073083490618072499)
            ·
              refine ⟨6709342609625235927108749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472895073083490618072499 6709342609625235927108749)
              ·
                refine ⟨2516003478609463472665781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6709342609625235927108749 2516003478609463472665781)
                ·
                  refine ⟨235875326119637200562417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2516003478609463472665781 235875326119637200562417)
                  ·
                    rfl

theorem cell23_4134290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_4134290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134290 prefixEnd_4134290 := by exact prefixLift 4134290
  have htrace : WordTrace (prefixWord ++ tailWord_4134290) baseStart_4134290 baseEnd_4134290 := by
    simpa [prefixWord, tailWord_4134290, baseEnd_4134290] using wordTrace_append hprefix tailTrace_4134290
  have hstable : (prefixWord ++ tailWord_4134290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134290).length < 2 ^ (prefixWord ++ tailWord_4134290).sum := by decide
  have hdescent : baseEnd_4134290 < baseStart_4134290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134315 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_4134315 : Nat := 118140960795 + 4134315 * 2 ^ 59
def prefixEnd_4134315 : Nat := 4983230072969 + 3 ^ 40 * 4134315 * 2
def baseEnd_4134315 : Nat := 2122890772093097207249137

theorem tailTrace_4134315 : CollatzResearch.WordTrace tailWord_4134315 prefixEnd_4134315 2122890772093097207249137 := by
  unfold tailWord_4134315
  simp only [CollatzResearch.WordTrace]
  refine ⟨150790856017090314632828399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100527237344726876421885599 150790856017090314632828399)
  ·
    refine ⟨226186284025635471949242599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150790856017090314632828399 226186284025635471949242599)
    ·
      refine ⟨339279426038453207923863899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226186284025635471949242599 339279426038453207923863899)
      ·
        refine ⟨508919139057679811885795849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339279426038453207923863899 508919139057679811885795849)
        ·
          refine ⟨381689354293259858914346887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508919139057679811885795849 381689354293259858914346887)
          ·
            refine ⟨572534031439889788371520331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381689354293259858914346887 572534031439889788371520331)
            ·
              refine ⟨858801047159834682557280497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572534031439889788371520331 858801047159834682557280497)
              ·
                refine ⟨644100785369876011917960373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858801047159834682557280497 644100785369876011917960373)
                ·
                  refine ⟨60384448628425876117308785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644100785369876011917960373 60384448628425876117308785)
                  ·
                    refine ⟨45288336471319407087981589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60384448628425876117308785 45288336471319407087981589)
                    ·
                      refine ⟨2122890772093097207249137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45288336471319407087981589 2122890772093097207249137)
                      ·
                        rfl

theorem cell23_4134315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_4134315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134315 prefixEnd_4134315 := by exact prefixLift 4134315
  have htrace : WordTrace (prefixWord ++ tailWord_4134315) baseStart_4134315 baseEnd_4134315 := by
    simpa [prefixWord, tailWord_4134315, baseEnd_4134315] using wordTrace_append hprefix tailTrace_4134315
  have hstable : (prefixWord ++ tailWord_4134315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134315).length < 2 ^ (prefixWord ++ tailWord_4134315).sum := by decide
  have hdescent : baseEnd_4134315 < baseStart_4134315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134322 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_4134322 : Nat := 118140960795 + 4134322 * 2 ^ 59
def prefixEnd_4134322 : Nat := 4983230072969 + 3 ^ 40 * 4134322 * 2
def baseEnd_4134322 : Nat := 2122894366457678679861605

theorem tailTrace_4134322 : CollatzResearch.WordTrace tailWord_4134322 prefixEnd_4134322 2122894366457678679861605 := by
  unfold tailWord_4134322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697777832016238707083305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100527407552043303218888813 37697777832016238707083305)
  ·
    refine ⟨28273333374012179030312479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37697777832016238707083305 28273333374012179030312479)
    ·
      refine ⟨42410000061018268545468719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28273333374012179030312479 42410000061018268545468719)
      ·
        refine ⟨63615000091527402818203079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42410000061018268545468719 63615000091527402818203079)
        ·
          refine ⟨95422500137291104227304619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63615000091527402818203079 95422500137291104227304619)
          ·
            refine ⟨143133750205936656340956929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95422500137291104227304619 143133750205936656340956929)
            ·
              refine ⟨107350312654452492255717697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143133750205936656340956929 107350312654452492255717697)
              ·
                refine ⟨80512734490839369191788273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107350312654452492255717697 80512734490839369191788273)
                ·
                  refine ⟨60384550868129526893841205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80512734490839369191788273 60384550868129526893841205)
                  ·
                    refine ⟨5661051643887143146297613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60384550868129526893841205 5661051643887143146297613)
                    ·
                      refine ⟨2122894366457678679861605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661051643887143146297613 2122894366457678679861605)
                      ·
                        rfl

theorem cell23_4134322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_4134322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134322 prefixEnd_4134322 := by exact prefixLift 4134322
  have htrace : WordTrace (prefixWord ++ tailWord_4134322) baseStart_4134322 baseEnd_4134322 := by
    simpa [prefixWord, tailWord_4134322, baseEnd_4134322] using wordTrace_append hprefix tailTrace_4134322
  have hstable : (prefixWord ++ tailWord_4134322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134322).length < 2 ^ (prefixWord ++ tailWord_4134322).sum := by decide
  have hdescent : baseEnd_4134322 < baseStart_4134322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134329 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 6]
def baseStart_4134329 : Nat := 118140960795 + 4134329 * 2 ^ 59
def prefixEnd_4134329 : Nat := 4983230072969 + 3 ^ 40 * 4134329 * 2
def baseEnd_4134329 : Nat := 235877551202473350274897

theorem tailTrace_4134329 : CollatzResearch.WordTrace tailWord_4134329 prefixEnd_4134329 235877551202473350274897 := by
  unfold tailWord_4134329
  simp only [CollatzResearch.WordTrace]
  refine ⟨150791366639039595023838041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100527577759359730015892027 150791366639039595023838041)
  ·
    refine ⟨113093524979279696267878531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150791366639039595023838041 113093524979279696267878531)
    ·
      refine ⟨169640287468919544401817797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113093524979279696267878531 169640287468919544401817797)
      ·
        refine ⟨31807553900422414575340837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169640287468919544401817797 31807553900422414575340837)
        ·
          refine ⟨5963916356329202732876407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31807553900422414575340837 5963916356329202732876407)
          ·
            refine ⟨8945874534493804099314611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963916356329202732876407 8945874534493804099314611)
            ·
              refine ⟨13418811801740706148971917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945874534493804099314611 13418811801740706148971917)
              ·
                refine ⟨5032054425652764805864469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418811801740706148971917 5032054425652764805864469)
                ·
                  refine ⟨235877551202473350274897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5032054425652764805864469 235877551202473350274897)
                  ·
                    rfl

theorem cell23_4134329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_4134329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134329 prefixEnd_4134329 := by exact prefixLift 4134329
  have htrace : WordTrace (prefixWord ++ tailWord_4134329) baseStart_4134329 baseEnd_4134329 := by
    simpa [prefixWord, tailWord_4134329, baseEnd_4134329] using wordTrace_append hprefix tailTrace_4134329
  have hstable : (prefixWord ++ tailWord_4134329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134329).length < 2 ^ (prefixWord ++ tailWord_4134329).sum := by decide
  have hdescent : baseEnd_4134329 < baseStart_4134329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134339 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 3]
def baseStart_4134339 : Nat := 118140960795 + 4134339 * 2 ^ 59
def prefixEnd_4134339 : Nat := 4983230072969 + 3 ^ 40 * 4134339 * 2
def baseEnd_4134339 : Nat := 2122903095628805113349027

theorem tailTrace_4134339 : CollatzResearch.WordTrace tailWord_4134339 prefixEnd_4134339 2122903095628805113349027 := by
  unfold tailWord_4134339
  simp only [CollatzResearch.WordTrace]
  refine ⟨150791731369003366731702071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100527820912668911154468047 150791731369003366731702071)
  ·
    refine ⟨226187597053505050097553107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150791731369003366731702071 226187597053505050097553107)
    ·
      refine ⟨339281395580257575146329661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226187597053505050097553107 339281395580257575146329661)
      ·
        refine ⟨127230523342596590679873623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339281395580257575146329661 127230523342596590679873623)
        ·
          refine ⟨190845785013894886019810435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127230523342596590679873623 190845785013894886019810435)
          ·
            refine ⟨286268677520842329029715653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190845785013894886019810435 286268677520842329029715653)
            ·
              refine ⟨53675377035157936693071685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286268677520842329029715653 53675377035157936693071685)
              ·
                refine ⟨10064133194092113129950941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53675377035157936693071685 10064133194092113129950941)
                ·
                  refine ⟨3774049947784542423731603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10064133194092113129950941 3774049947784542423731603)
                  ·
                    refine ⟨5661074921676813635597405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774049947784542423731603 5661074921676813635597405)
                    ·
                      refine ⟨2122903095628805113349027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661074921676813635597405 2122903095628805113349027)
                      ·
                        rfl

theorem cell23_4134339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_4134339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134339 prefixEnd_4134339 := by exact prefixLift 4134339
  have htrace : WordTrace (prefixWord ++ tailWord_4134339) baseStart_4134339 baseEnd_4134339 := by
    simpa [prefixWord, tailWord_4134339, baseEnd_4134339] using wordTrace_append hprefix tailTrace_4134339
  have hstable : (prefixWord ++ tailWord_4134339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134339).length < 2 ^ (prefixWord ++ tailWord_4134339).sum := by decide
  have hdescent : baseEnd_4134339 < baseStart_4134339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134396 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_4134396 : Nat := 118140960795 + 4134396 * 2 ^ 59
def prefixEnd_4134396 : Nat := 4983230072969 + 3 ^ 40 * 4134396 * 2
def baseEnd_4134396 : Nat := 2122932364026111390336265

theorem tailTrace_4134396 : CollatzResearch.WordTrace tailWord_4134396 prefixEnd_4134396 2122932364026111390336265 := by
  unfold tailWord_4134396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75396905164898432733263521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100529206886531243644351361 75396905164898432733263521)
  ·
    refine ⟨56547678873673824549947641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75396905164898432733263521 56547678873673824549947641)
    ·
      refine ⟨42410759155255368412460731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56547678873673824549947641 42410759155255368412460731)
      ·
        refine ⟨63616138732883052618691097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42410759155255368412460731 63616138732883052618691097)
        ·
          refine ⟨47712104049662289464018323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63616138732883052618691097 47712104049662289464018323)
          ·
            refine ⟨71568156074493434196027485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47712104049662289464018323 71568156074493434196027485)
            ·
              refine ⟨26838058527935037823510307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71568156074493434196027485 26838058527935037823510307)
              ·
                refine ⟨40257087791902556735265461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26838058527935037823510307 40257087791902556735265461)
                ·
                  refine ⟨3774101980490864693931137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40257087791902556735265461 3774101980490864693931137)
                  ·
                    refine ⟨2830576485368148520448353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3774101980490864693931137 2830576485368148520448353)
                    ·
                      refine ⟨2122932364026111390336265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830576485368148520448353 2122932364026111390336265)
                      ·
                        rfl

theorem cell23_4134396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_4134396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134396 prefixEnd_4134396 := by exact prefixLift 4134396
  have htrace : WordTrace (prefixWord ++ tailWord_4134396) baseStart_4134396 baseEnd_4134396 := by
    simpa [prefixWord, tailWord_4134396, baseEnd_4134396] using wordTrace_append hprefix tailTrace_4134396
  have hstable : (prefixWord ++ tailWord_4134396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134396).length < 2 ^ (prefixWord ++ tailWord_4134396).sum := by decide
  have hdescent : baseEnd_4134396 < baseStart_4134396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134440 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4134440 : Nat := 118140960795 + 4134440 * 2 ^ 59
def prefixEnd_4134440 : Nat := 4983230072969 + 3 ^ 40 * 4134440 * 2
def baseEnd_4134440 : Nat := 707651652391636406062021

theorem tailTrace_4134440 : CollatzResearch.WordTrace tailWord_4134440 prefixEnd_4134440 707651652391636406062021 := by
  unfold tailWord_4134440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75397707570818730490564387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100530276761091640654085849 75397707570818730490564387)
  ·
    refine ⟨113096561356228095735846581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75397707570818730490564387 113096561356228095735846581)
    ·
      refine ⟨10602802627146383975235617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113096561356228095735846581 10602802627146383975235617)
      ·
        refine ⟨7952101970359787981426713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10602802627146383975235617 7952101970359787981426713)
        ·
          refine ⟨5964076477769840986070035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7952101970359787981426713 5964076477769840986070035)
          ·
            refine ⟨8946114716654761479105053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964076477769840986070035 8946114716654761479105053)
            ·
              refine ⟨3354793018745535554664395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8946114716654761479105053 3354793018745535554664395)
              ·
                refine ⟨5032189528118303331996593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354793018745535554664395 5032189528118303331996593)
                ·
                  refine ⟨3774142146088727498997445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032189528118303331996593 3774142146088727498997445)
                  ·
                    refine ⟨707651652391636406062021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774142146088727498997445 707651652391636406062021)
                    ·
                      rfl

theorem cell23_4134440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4134440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134440 prefixEnd_4134440 := by exact prefixLift 4134440
  have htrace : WordTrace (prefixWord ++ tailWord_4134440) baseStart_4134440 baseEnd_4134440 := by
    simpa [prefixWord, tailWord_4134440, baseEnd_4134440] using wordTrace_append hprefix tailTrace_4134440
  have hstable : (prefixWord ++ tailWord_4134440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134440).length < 2 ^ (prefixWord ++ tailWord_4134440).sum := by decide
  have hdescent : baseEnd_4134440 < baseStart_4134440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134519 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_4134519 : Nat := 118140960795 + 4134519 * 2 ^ 59
def prefixEnd_4134519 : Nat := 4983230072969 + 3 ^ 40 * 4134519 * 2
def baseEnd_4134519 : Nat := 2122995522146614409098199

theorem tailTrace_4134519 : CollatzResearch.WordTrace tailWord_4134519 prefixEnd_4134519 2122995522146614409098199 := by
  unfold tailWord_4134519
  simp only [CollatzResearch.WordTrace]
  refine ⟨150798296508351257473254611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100532197672234171648836407 150798296508351257473254611)
  ·
    refine ⟨226197444762526886209881917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150798296508351257473254611 226197444762526886209881917)
    ·
      refine ⟨84824041785947582328705719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226197444762526886209881917 84824041785947582328705719)
      ·
        refine ⟨127236062678921373493058579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84824041785947582328705719 127236062678921373493058579)
        ·
          refine ⟨190854094018382060239587869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127236062678921373493058579 190854094018382060239587869)
          ·
            refine ⟨71570285256893272589845451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190854094018382060239587869 71570285256893272589845451)
            ·
              refine ⟨107355427885339908884768177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71570285256893272589845451 107355427885339908884768177)
              ·
                refine ⟨80516570914004931663576133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107355427885339908884768177 80516570914004931663576133)
                ·
                  refine ⟨15096857046375924686920525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80516570914004931663576133 15096857046375924686920525)
                  ·
                    refine ⟨5661321392390971757595197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15096857046375924686920525 5661321392390971757595197)
                    ·
                      refine ⟨2122995522146614409098199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661321392390971757595197 2122995522146614409098199)
                      ·
                        rfl

theorem cell23_4134519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_4134519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134519 prefixEnd_4134519 := by exact prefixLift 4134519
  have htrace : WordTrace (prefixWord ++ tailWord_4134519) baseStart_4134519 baseEnd_4134519 := by
    simpa [prefixWord, tailWord_4134519, baseEnd_4134519] using wordTrace_append hprefix tailTrace_4134519
  have hstable : (prefixWord ++ tailWord_4134519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134519).length < 2 ^ (prefixWord ++ tailWord_4134519).sum := by decide
  have hdescent : baseEnd_4134519 < baseStart_4134519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134539 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 2, 5]
def baseStart_4134539 : Nat := 118140960795 + 4134539 * 2 ^ 59
def prefixEnd_4134539 : Nat := 4983230072969 + 3 ^ 40 * 4134539 * 2
def baseEnd_4134539 : Nat := 707668597253234776949369

theorem tailTrace_4134539 : CollatzResearch.WordTrace tailWord_4134539 prefixEnd_4134539 707668597253234776949369 := by
  unfold tailWord_4134539
  simp only [CollatzResearch.WordTrace]
  refine ⟨150799025968278800888982671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100532683978852533925988447 150799025968278800888982671)
  ·
    refine ⟨226198538952418201333474007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150799025968278800888982671 226198538952418201333474007)
    ·
      refine ⟨339297808428627302000211011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226198538952418201333474007 339297808428627302000211011)
      ·
        refine ⟨508946712642940953000316517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339297808428627302000211011 508946712642940953000316517)
        ·
          refine ⟨95427508620551428687559347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508946712642940953000316517 95427508620551428687559347)
          ·
            refine ⟨143141262930827143031339021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95427508620551428687559347 143141262930827143031339021)
            ·
              refine ⟨53677973599060178636752133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143141262930827143031339021 53677973599060178636752133)
              ·
                refine ⟨10064620049823783494391025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53677973599060178636752133 10064620049823783494391025)
                ·
                  refine ⟨7548465037367837620793269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10064620049823783494391025 7548465037367837620793269)
                  ·
                    refine ⟨707668597253234776949369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7548465037367837620793269 707668597253234776949369)
                    ·
                      rfl

theorem cell23_4134539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 5].length) (baseStart_4134539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134539 prefixEnd_4134539 := by exact prefixLift 4134539
  have htrace : WordTrace (prefixWord ++ tailWord_4134539) baseStart_4134539 baseEnd_4134539 := by
    simpa [prefixWord, tailWord_4134539, baseEnd_4134539] using wordTrace_append hprefix tailTrace_4134539
  have hstable : (prefixWord ++ tailWord_4134539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134539).length < 2 ^ (prefixWord ++ tailWord_4134539).sum := by decide
  have hdescent : baseEnd_4134539 < baseStart_4134539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134576 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_4134576 : Nat := 118140960795 + 4134576 * 2 ^ 59
def prefixEnd_4134576 : Nat := 4983230072969 + 3 ^ 40 * 4134576 * 2
def baseEnd_4134576 : Nat := 2123024790543920686085437

theorem tailTrace_4134576 : CollatzResearch.WordTrace tailWord_4134576 prefixEnd_4134576 2123024790543920686085437 := by
  unfold tailWord_4134576
  simp only [CollatzResearch.WordTrace]
  refine ⟨75400187734572378104039791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100533583646096504138719721 75400187734572378104039791)
  ·
    refine ⟨113100281601858567156059687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75400187734572378104039791 113100281601858567156059687)
    ·
      refine ⟨169650422402787850734089531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113100281601858567156059687 169650422402787850734089531)
      ·
        refine ⟨254475633604181776101134297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169650422402787850734089531 254475633604181776101134297)
        ·
          refine ⟨190856725203136332075850723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254475633604181776101134297 190856725203136332075850723)
          ·
            refine ⟨286285087804704498113776085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190856725203136332075850723 286285087804704498113776085)
            ·
              refine ⟨6709806745422761674541627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 286285087804704498113776085 6709806745422761674541627)
              ·
                refine ⟨10064710118134142511812441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709806745422761674541627 10064710118134142511812441)
                ·
                  refine ⟨7548532588600606883859331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10064710118134142511812441 7548532588600606883859331)
                  ·
                    refine ⟨11322798882900910325788997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548532588600606883859331 11322798882900910325788997)
                    ·
                      refine ⟨2123024790543920686085437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11322798882900910325788997 2123024790543920686085437)
                      ·
                        rfl

theorem cell23_4134576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_4134576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134576 prefixEnd_4134576 := by exact prefixLift 4134576
  have htrace : WordTrace (prefixWord ++ tailWord_4134576) baseStart_4134576 baseEnd_4134576 := by
    simpa [prefixWord, tailWord_4134576, baseEnd_4134576] using wordTrace_append hprefix tailTrace_4134576
  have hstable : (prefixWord ++ tailWord_4134576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134576).length < 2 ^ (prefixWord ++ tailWord_4134576).sum := by decide
  have hdescent : baseEnd_4134576 < baseStart_4134576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134589 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4134589 : Nat := 118140960795 + 4134589 * 2 ^ 59
def prefixEnd_4134589 : Nat := 4983230072969 + 3 ^ 40 * 4134589 * 2
def baseEnd_4134589 : Nat := 2123031465792429135222877

theorem tailTrace_4134589 : CollatzResearch.WordTrace tailWord_4134589 prefixEnd_4134589 2123031465792429135222877 := by
  unfold tailWord_4134589
  simp only [CollatzResearch.WordTrace]
  refine ⟨150800849618097659428302821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100533899745398439618868547 150800849618097659428302821)
  ·
    refine ⟨28275159303393311142806779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150800849618097659428302821 28275159303393311142806779)
    ·
      refine ⟨42412738955089966714210169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28275159303393311142806779 42412738955089966714210169)
      ·
        refine ⟨31809554216317475035657627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42412738955089966714210169 31809554216317475035657627)
        ·
          refine ⟨47714331324476212553486441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31809554216317475035657627 47714331324476212553486441)
          ·
            refine ⟨35785748493357159415114831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47714331324476212553486441 35785748493357159415114831)
            ·
              refine ⟨53678622740035739122672247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35785748493357159415114831 53678622740035739122672247)
              ·
                refine ⟨80517934110053608684008371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53678622740035739122672247 80517934110053608684008371)
                ·
                  refine ⟨120776901165080413026012557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80517934110053608684008371 120776901165080413026012557)
                  ·
                    refine ⟨45291337936905154884754709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120776901165080413026012557 45291337936905154884754709)
                    ·
                      refine ⟨2123031465792429135222877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45291337936905154884754709 2123031465792429135222877)
                      ·
                        rfl

theorem cell23_4134589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4134589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134589 prefixEnd_4134589 := by exact prefixLift 4134589
  have htrace : WordTrace (prefixWord ++ tailWord_4134589) baseStart_4134589 baseEnd_4134589 := by
    simpa [prefixWord, tailWord_4134589, baseEnd_4134589] using wordTrace_append hprefix tailTrace_4134589
  have hstable : (prefixWord ++ tailWord_4134589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134589).length < 2 ^ (prefixWord ++ tailWord_4134589).sum := by decide
  have hdescent : baseEnd_4134589 < baseStart_4134589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134599 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 8]
def baseStart_4134599 : Nat := 118140960795 + 4134599 * 2 ^ 59
def prefixEnd_4134599 : Nat := 4983230072969 + 3 ^ 40 * 4134599 * 2
def baseEnd_4134599 : Nat := 235892955622108232899759

theorem tailTrace_4134599 : CollatzResearch.WordTrace tailWord_4134599 prefixEnd_4134599 235892955622108232899759 := by
  unfold tailWord_4134599
  simp only [CollatzResearch.WordTrace]
  refine ⟨150801214348061431136166851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100534142898707620757444567 150801214348061431136166851)
  ·
    refine ⟨226201821522092146704250277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150801214348061431136166851 226201821522092146704250277)
    ·
      refine ⟨42412841535392277507046927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226201821522092146704250277 42412841535392277507046927)
      ·
        refine ⟨63619262303088416260570391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42412841535392277507046927 63619262303088416260570391)
        ·
          refine ⟨95428893454632624390855587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63619262303088416260570391 95428893454632624390855587)
          ·
            refine ⟨143143340181948936586283381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95428893454632624390855587 143143340181948936586283381)
            ·
              refine ⟨13419688142057712804964067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143143340181948936586283381 13419688142057712804964067)
              ·
                refine ⟨20129532213086569207446101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13419688142057712804964067 20129532213086569207446101)
                ·
                  refine ⟨235892955622108232899759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20129532213086569207446101 235892955622108232899759)
                  ·
                    rfl

theorem cell23_4134599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 8].length) (baseStart_4134599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134599 prefixEnd_4134599 := by exact prefixLift 4134599
  have htrace : WordTrace (prefixWord ++ tailWord_4134599) baseStart_4134599 baseEnd_4134599 := by
    simpa [prefixWord, tailWord_4134599, baseEnd_4134599] using wordTrace_append hprefix tailTrace_4134599
  have hstable : (prefixWord ++ tailWord_4134599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134599).length < 2 ^ (prefixWord ++ tailWord_4134599).sum := by decide
  have hdescent : baseEnd_4134599 < baseStart_4134599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134637 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_4134637 : Nat := 118140960795 + 4134637 * 2 ^ 59
def prefixEnd_4134637 : Nat := 4983230072969 + 3 ^ 40 * 4134637 * 2
def baseEnd_4134637 : Nat := 707685370954614982474219

theorem tailTrace_4134637 : CollatzResearch.WordTrace tailWord_4134637 prefixEnd_4134637 707685370954614982474219 := by
  unfold tailWord_4134637
  simp only [CollatzResearch.WordTrace]
  refine ⟨150802600321923763626050165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100535066881282509084033443 150802600321923763626050165)
  ·
    refine ⟨14137743780180352839942203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150802600321923763626050165 14137743780180352839942203)
    ·
      refine ⟨21206615670270529259913305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14137743780180352839942203 21206615670270529259913305)
      ·
        refine ⟨15904961752702896944934979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21206615670270529259913305 15904961752702896944934979)
        ·
          refine ⟨23857442629054345417402469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15904961752702896944934979 23857442629054345417402469)
          ·
            refine ⟨4473270492947689765762963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23857442629054345417402469 4473270492947689765762963)
            ·
              refine ⟨6709905739421534648644445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473270492947689765762963 6709905739421534648644445)
              ·
                refine ⟨2516214652283075493241667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6709905739421534648644445 2516214652283075493241667)
                ·
                  refine ⟨3774321978424613239862501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516214652283075493241667 3774321978424613239862501)
                  ·
                    refine ⟨707685370954614982474219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774321978424613239862501 707685370954614982474219)
                    ·
                      rfl

theorem cell23_4134637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_4134637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134637 prefixEnd_4134637 := by exact prefixLift 4134637
  have htrace : WordTrace (prefixWord ++ tailWord_4134637) baseStart_4134637 baseEnd_4134637 := by
    simpa [prefixWord, tailWord_4134637, baseEnd_4134637] using wordTrace_append hprefix tailTrace_4134637
  have hstable : (prefixWord ++ tailWord_4134637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134637).length < 2 ^ (prefixWord ++ tailWord_4134637).sum := by decide
  have hdescent : baseEnd_4134637 < baseStart_4134637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134654 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_4134654 : Nat := 118140960795 + 4134654 * 2 ^ 59
def prefixEnd_4134654 : Nat := 4983230072969 + 3 ^ 40 * 4134654 * 2
def baseEnd_4134654 : Nat := 707688280678323793636693

theorem tailTrace_4134654 : CollatzResearch.WordTrace tailWord_4134654 prefixEnd_4134654 707688280678323793636693 := by
  unfold tailWord_4134654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850402545357771941177377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100535480241908117019612677 18850402545357771941177377)
  ·
    refine ⟨14137801909018328955883033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18850402545357771941177377 14137801909018328955883033)
    ·
      refine ⟨10603351431763746716912275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14137801909018328955883033 10603351431763746716912275)
      ·
        refine ⟨15905027147645620075368413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10603351431763746716912275 15905027147645620075368413)
        ·
          refine ⟨5964385180367107528263155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15905027147645620075368413 5964385180367107528263155)
          ·
            refine ⟨8946577770550661292394733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964385180367107528263155 8946577770550661292394733)
            ·
              refine ⟨3354966663956497984648025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8946577770550661292394733 3354966663956497984648025)
              ·
                refine ⟨2516224997967373488486019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354966663956497984648025 2516224997967373488486019)
                ·
                  refine ⟨3774337496951060232729029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516224997967373488486019 3774337496951060232729029)
                  ·
                    refine ⟨707688280678323793636693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774337496951060232729029 707688280678323793636693)
                    ·
                      rfl

theorem cell23_4134654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_4134654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134654 prefixEnd_4134654 := by exact prefixLift 4134654
  have htrace : WordTrace (prefixWord ++ tailWord_4134654) baseStart_4134654 baseEnd_4134654 := by
    simpa [prefixWord, tailWord_4134654, baseEnd_4134654] using wordTrace_append hprefix tailTrace_4134654
  have hstable : (prefixWord ++ tailWord_4134654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134654).length < 2 ^ (prefixWord ++ tailWord_4134654).sum := by decide
  have hdescent : baseEnd_4134654 < baseStart_4134654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134660 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4134660 : Nat := 118140960795 + 4134660 * 2 ^ 59
def prefixEnd_4134660 : Nat := 4983230072969 + 3 ^ 40 * 4134660 * 2
def baseEnd_4134660 : Nat := 2123067922918898357435051

theorem tailTrace_4134660 : CollatzResearch.WordTrace tailWord_4134660 prefixEnd_4134660 2123067922918898357435051 := by
  unfold tailWord_4134660
  simp only [CollatzResearch.WordTrace]
  refine ⟨75401719600420219277068717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100535626133893625702758289 75401719600420219277068717)
  ·
    refine ⟨28275644850157582228900769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75401719600420219277068717 28275644850157582228900769)
    ·
      refine ⟨21206733637618186671675577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28275644850157582228900769 21206733637618186671675577)
      ·
        refine ⟨15905050228213640003756683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21206733637618186671675577 15905050228213640003756683)
        ·
          refine ⟨23857575342320460005635025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15905050228213640003756683 23857575342320460005635025)
          ·
            refine ⟨17893181506740345004226269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23857575342320460005635025 17893181506740345004226269)
            ·
              refine ⟨6709943065027629376584851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17893181506740345004226269 6709943065027629376584851)
              ·
                refine ⟨10064914597541444064877277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709943065027629376584851 10064914597541444064877277)
                ·
                  refine ⟨3774342974078041524328979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10064914597541444064877277 3774342974078041524328979)
                  ·
                    refine ⟨5661514461117062286493469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774342974078041524328979 5661514461117062286493469)
                    ·
                      refine ⟨2123067922918898357435051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661514461117062286493469 2123067922918898357435051)
                      ·
                        rfl

theorem cell23_4134660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4134660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134660 prefixEnd_4134660 := by exact prefixLift 4134660
  have htrace : WordTrace (prefixWord ++ tailWord_4134660) baseStart_4134660 baseEnd_4134660 := by
    simpa [prefixWord, tailWord_4134660, baseEnd_4134660] using wordTrace_append hprefix tailTrace_4134660
  have hstable : (prefixWord ++ tailWord_4134660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134660).length < 2 ^ (prefixWord ++ tailWord_4134660).sum := by decide
  have hdescent : baseEnd_4134660 < baseStart_4134660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134699 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_4134699 : Nat := 118140960795 + 4134699 * 2 ^ 59
def prefixEnd_4134699 : Nat := 4983230072969 + 3 ^ 40 * 4134699 * 2
def baseEnd_4134699 : Nat := 2123087948664423704847371

theorem tailTrace_4134699 : CollatzResearch.WordTrace tailWord_4134699 prefixEnd_4134699 2123087948664423704847371 := by
  unfold tailWord_4134699
  simp only [CollatzResearch.WordTrace]
  refine ⟨150804861647699148214807151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100536574431799432143204767 150804861647699148214807151)
  ·
    refine ⟨226207292471548722322210727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150804861647699148214807151 226207292471548722322210727)
    ·
      refine ⟨339310938707323083483316091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226207292471548722322210727 339310938707323083483316091)
      ·
        refine ⟨508966408060984625224974137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339310938707323083483316091 508966408060984625224974137)
        ·
          refine ⟨381724806045738468918730603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508966408060984625224974137 381724806045738468918730603)
          ·
            refine ⟨572587209068607703378095905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381724806045738468918730603 572587209068607703378095905)
            ·
              refine ⟨429440406801455777533571929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572587209068607703378095905 429440406801455777533571929)
              ·
                refine ⟨322080305101091833150178947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429440406801455777533571929 322080305101091833150178947)
                ·
                  refine ⟨483120457651637749725268421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322080305101091833150178947 483120457651637749725268421)
                  ·
                    refine ⟨90585085809682078073487829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483120457651637749725268421 90585085809682078073487829)
                    ·
                      refine ⟨2123087948664423704847371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90585085809682078073487829 2123087948664423704847371)
                      ·
                        rfl

theorem cell23_4134699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_4134699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134699 prefixEnd_4134699 := by exact prefixLift 4134699
  have htrace : WordTrace (prefixWord ++ tailWord_4134699) baseStart_4134699 baseEnd_4134699 := by
    simpa [prefixWord, tailWord_4134699, baseEnd_4134699] using wordTrace_append hprefix tailTrace_4134699
  have hstable : (prefixWord ++ tailWord_4134699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134699).length < 2 ^ (prefixWord ++ tailWord_4134699).sum := by decide
  have hdescent : baseEnd_4134699 < baseStart_4134699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134700 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_4134700 : Nat := 118140960795 + 4134700 * 2 ^ 59
def prefixEnd_4134700 : Nat := 4983230072969 + 3 ^ 40 * 4134700 * 2
def baseEnd_4134700 : Nat := 2123088462145078200934867

theorem tailTrace_4134700 : CollatzResearch.WordTrace tailWord_4134700 prefixEnd_4134700 2123088462145078200934867 := by
  unfold tailWord_4134700
  simp only [CollatzResearch.WordTrace]
  refine ⟨75402449060347762692796777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100536598747130350257062369 75402449060347762692796777)
  ·
    refine ⟨56551836795260822019597583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75402449060347762692796777 56551836795260822019597583)
    ·
      refine ⟨84827755192891233029396375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56551836795260822019597583 84827755192891233029396375)
      ·
        refine ⟨127241632789336849544094563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84827755192891233029396375 127241632789336849544094563)
        ·
          refine ⟨190862449184005274316141845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127241632789336849544094563 190862449184005274316141845)
          ·
            refine ⟨8946677305500247233569149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190862449184005274316141845 8946677305500247233569149)
            ·
              refine ⟨3355003989562592712588431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8946677305500247233569149 3355003989562592712588431)
              ·
                refine ⟨5032505984343889068882647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355003989562592712588431 5032505984343889068882647)
                ·
                  refine ⟨7548758976515833603323971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032505984343889068882647 7548758976515833603323971)
                  ·
                    refine ⟨11323138464773750404985957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548758976515833603323971 11323138464773750404985957)
                    ·
                      refine ⟨2123088462145078200934867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11323138464773750404985957 2123088462145078200934867)
                      ·
                        rfl

theorem cell23_4134700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_4134700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134700 prefixEnd_4134700 := by exact prefixLift 4134700
  have htrace : WordTrace (prefixWord ++ tailWord_4134700) baseStart_4134700 baseEnd_4134700 := by
    simpa [prefixWord, tailWord_4134700, baseEnd_4134700] using wordTrace_append hprefix tailTrace_4134700
  have hstable : (prefixWord ++ tailWord_4134700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134700).length < 2 ^ (prefixWord ++ tailWord_4134700).sum := by decide
  have hdescent : baseEnd_4134700 < baseStart_4134700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134746 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_4134746 : Nat := 118140960795 + 4134746 * 2 ^ 59
def prefixEnd_4134746 : Nat := 4983230072969 + 3 ^ 40 * 4134746 * 2
def baseEnd_4134746 : Nat := 2123112082255185020959655

theorem tailTrace_4134746 : CollatzResearch.WordTrace tailWord_4134746 prefixEnd_4134746 2123112082255185020959655 := by
  unfold tailWord_4134746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37701643969632218810442023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100537717252352583494512061 37701643969632218810442023)
  ·
    refine ⟨56552465954448328215663035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37701643969632218810442023 56552465954448328215663035)
    ·
      refine ⟨84828698931672492323494553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56552465954448328215663035 84828698931672492323494553)
      ·
        refine ⟨63621524198754369242620915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84828698931672492323494553 63621524198754369242620915)
        ·
          refine ⟨95432286298131553863931373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63621524198754369242620915 95432286298131553863931373)
          ·
            refine ⟨35787107361799332698974265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95432286298131553863931373 35787107361799332698974265)
            ·
              refine ⟨26840330521349499524230699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35787107361799332698974265 26840330521349499524230699)
              ·
                refine ⟨40260495782024249286346049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26840330521349499524230699 40260495782024249286346049)
                ·
                  refine ⟨30195371836518186964759537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40260495782024249286346049 30195371836518186964759537)
                  ·
                    refine ⟨22646528877388640223569653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30195371836518186964759537 22646528877388640223569653)
                    ·
                      refine ⟨2123112082255185020959655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22646528877388640223569653 2123112082255185020959655)
                      ·
                        rfl

theorem cell23_4134746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_4134746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134746 prefixEnd_4134746 := by exact prefixLift 4134746
  have htrace : WordTrace (prefixWord ++ tailWord_4134746) baseStart_4134746 baseEnd_4134746 := by
    simpa [prefixWord, tailWord_4134746, baseEnd_4134746] using wordTrace_append hprefix tailTrace_4134746
  have hstable : (prefixWord ++ tailWord_4134746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134746).length < 2 ^ (prefixWord ++ tailWord_4134746).sum := by decide
  have hdescent : baseEnd_4134746 < baseStart_4134746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134754 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4134754 : Nat := 118140960795 + 4134754 * 2 ^ 59
def prefixEnd_4134754 : Nat := 4983230072969 + 3 ^ 40 * 4134754 * 2
def baseEnd_4134754 : Nat := 2123116190100420989659619

theorem tailTrace_4134754 : CollatzResearch.WordTrace tailWord_4134754 prefixEnd_4134754 2123116190100420989659619 := by
  unfold tailWord_4134754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37701716915624973152014829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100537911774999928405372877 37701716915624973152014829)
  ·
    refine ⟨14138143843359364932005561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37701716915624973152014829 14138143843359364932005561)
    ·
      refine ⟨10603607882519523699004171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14138143843359364932005561 10603607882519523699004171)
      ·
        refine ⟨15905411823779285548506257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10603607882519523699004171 15905411823779285548506257)
        ·
          refine ⟨11929058867834464161379693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15905411823779285548506257 11929058867834464161379693)
          ·
            refine ⟨4473397075437924060517385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11929058867834464161379693 4473397075437924060517385)
            ·
              refine ⟨3355047806578443045388039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473397075437924060517385 3355047806578443045388039)
              ·
                refine ⟨5032571709867664568082059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355047806578443045388039 5032571709867664568082059)
                ·
                  refine ⟨7548857564801496852123089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032571709867664568082059 7548857564801496852123089)
                  ·
                    refine ⟨5661643173601122639092317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7548857564801496852123089 5661643173601122639092317)
                    ·
                      refine ⟨2123116190100420989659619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661643173601122639092317 2123116190100420989659619)
                      ·
                        rfl

theorem cell23_4134754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4134754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134754 prefixEnd_4134754 := by exact prefixLift 4134754
  have htrace : WordTrace (prefixWord ++ tailWord_4134754) baseStart_4134754 baseEnd_4134754 := by
    simpa [prefixWord, tailWord_4134754, baseEnd_4134754] using wordTrace_append hprefix tailTrace_4134754
  have hstable : (prefixWord ++ tailWord_4134754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134754).length < 2 ^ (prefixWord ++ tailWord_4134754).sum := by decide
  have hdescent : baseEnd_4134754 < baseStart_4134754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134794 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4134794 : Nat := 118140960795 + 4134794 * 2 ^ 59
def prefixEnd_4134794 : Nat := 4983230072969 + 3 ^ 40 * 4134794 * 2
def baseEnd_4134794 : Nat := 2123136729326600833159435

theorem tailTrace_4134794 : CollatzResearch.WordTrace tailWord_4134794 prefixEnd_4134794 2123136729326600833159435 := by
  unfold tailWord_4134794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37702081645588744859878859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100538884388236652959676957 37702081645588744859878859)
  ·
    refine ⟨56553122468383117289818289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37702081645588744859878859 56553122468383117289818289)
    ·
      refine ⟨42414841851287337967363717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56553122468383117289818289 42414841851287337967363717)
      ·
        refine ⟨7952782847116375868880697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42414841851287337967363717 7952782847116375868880697)
        ·
          refine ⟨5964587135337281901660523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7952782847116375868880697 5964587135337281901660523)
          ·
            refine ⟨8946880703005922852490785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964587135337281901660523 8946880703005922852490785)
            ·
              refine ⟨6710160527254442139368089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8946880703005922852490785 6710160527254442139368089)
              ·
                refine ⟨5032620395440831604526067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710160527254442139368089 5032620395440831604526067)
                ·
                  refine ⟨7548930593161247406789101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032620395440831604526067 7548930593161247406789101)
                  ·
                    refine ⟨2830848972435467777545913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7548930593161247406789101 2830848972435467777545913)
                    ·
                      refine ⟨2123136729326600833159435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830848972435467777545913 2123136729326600833159435)
                      ·
                        rfl

theorem cell23_4134794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4134794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134794 prefixEnd_4134794 := by exact prefixLift 4134794
  have htrace : WordTrace (prefixWord ++ tailWord_4134794) baseStart_4134794 baseEnd_4134794 := by
    simpa [prefixWord, tailWord_4134794, baseEnd_4134794] using wordTrace_append hprefix tailTrace_4134794
  have hstable : (prefixWord ++ tailWord_4134794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134794).length < 2 ^ (prefixWord ++ tailWord_4134794).sum := by decide
  have hdescent : baseEnd_4134794 < baseStart_4134794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134860 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_4134860 : Nat := 118140960795 + 4134860 * 2 ^ 59
def prefixEnd_4134860 : Nat := 4983230072969 + 3 ^ 40 * 4134860 * 2
def baseEnd_4134860 : Nat := 707723539683265858311377

theorem tailTrace_4134860 : CollatzResearch.WordTrace tailWord_4134860 prefixEnd_4134860 707723539683265858311377 := by
  unfold tailWord_4134860
  simp only [CollatzResearch.WordTrace]
  refine ⟨75405366900057936355709017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100540489200077248474278689 75405366900057936355709017)
  ·
    refine ⟨56554025175043452266781763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75405366900057936355709017 56554025175043452266781763)
    ·
      refine ⟨84831037762565178400172645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56554025175043452266781763 84831037762565178400172645)
      ·
        refine ⟨15905819580480970950032371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84831037762565178400172645 15905819580480970950032371)
        ·
          refine ⟨23858729370721456425048557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15905819580480970950032371 23858729370721456425048557)
          ·
            refine ⟨8947023514020546159393209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23858729370721456425048557 8947023514020546159393209)
            ·
              refine ⟨6710267635515409619544907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8947023514020546159393209 6710267635515409619544907)
              ·
                refine ⟨10065401453273114429317361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710267635515409619544907 10065401453273114429317361)
                ·
                  refine ⟨7549051089954835821988021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10065401453273114429317361 7549051089954835821988021)
                  ·
                    refine ⟨707723539683265858311377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7549051089954835821988021 707723539683265858311377)
                    ·
                      rfl

theorem cell23_4134860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_4134860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134860 prefixEnd_4134860 := by exact prefixLift 4134860
  have htrace : WordTrace (prefixWord ++ tailWord_4134860) baseStart_4134860 baseEnd_4134860 := by
    simpa [prefixWord, tailWord_4134860, baseEnd_4134860] using wordTrace_append hprefix tailTrace_4134860
  have hstable : (prefixWord ++ tailWord_4134860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134860).length < 2 ^ (prefixWord ++ tailWord_4134860).sum := by decide
  have hdescent : baseEnd_4134860 < baseStart_4134860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134890 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_4134890 : Nat := 118140960795 + 4134890 * 2 ^ 59
def prefixEnd_4134890 : Nat := 4983230072969 + 3 ^ 40 * 4134890 * 2
def baseEnd_4134890 : Nat := 707728674489810819186331

theorem tailTrace_4134890 : CollatzResearch.WordTrace tailWord_4134890 prefixEnd_4134890 707728674489810819186331 := by
  unfold tailWord_4134890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37702956997501796958752531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100541218660004791890006749 37702956997501796958752531)
  ·
    refine ⟨56554435496252695438128797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37702956997501796958752531 56554435496252695438128797)
    ·
      refine ⟨21207913311094760789298299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56554435496252695438128797 21207913311094760789298299)
      ·
        refine ⟨31811869966642141183947449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207913311094760789298299 31811869966642141183947449)
        ·
          refine ⟨23858902474981605887960587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31811869966642141183947449 23858902474981605887960587)
          ·
            refine ⟨35788353712472408831940881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23858902474981605887960587 35788353712472408831940881)
            ·
              refine ⟨26841265284354306623955661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35788353712472408831940881 26841265284354306623955661)
              ·
                refine ⟨10065474481632864983983373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26841265284354306623955661 10065474481632864983983373)
                ·
                  refine ⟨3774552930612324368993765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10065474481632864983983373 3774552930612324368993765)
                  ·
                    refine ⟨707728674489810819186331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774552930612324368993765 707728674489810819186331)
                    ·
                      rfl

theorem cell23_4134890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_4134890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134890 prefixEnd_4134890 := by exact prefixLift 4134890
  have htrace : WordTrace (prefixWord ++ tailWord_4134890) baseStart_4134890 baseEnd_4134890 := by
    simpa [prefixWord, tailWord_4134890, baseEnd_4134890] using wordTrace_append hprefix tailTrace_4134890
  have hstable : (prefixWord ++ tailWord_4134890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134890).length < 2 ^ (prefixWord ++ tailWord_4134890).sum := by decide
  have hdescent : baseEnd_4134890 < baseStart_4134890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134897 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_4134897 : Nat := 118140960795 + 4134897 * 2 ^ 59
def prefixEnd_4134897 : Nat := 4983230072969 + 3 ^ 40 * 4134897 * 2
def baseEnd_4134897 : Nat := 2123189617834013930171461

theorem tailTrace_4134897 : CollatzResearch.WordTrace tailWord_4134897 prefixEnd_4134897 2123189617834013930171461 := by
  unfold tailWord_4134897
  simp only [CollatzResearch.WordTrace]
  refine ⟨150812083300981828030514945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100541388867321218687009963 150812083300981828030514945)
  ·
    refine ⟨113109062475736371022886209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150812083300981828030514945 113109062475736371022886209)
    ·
      refine ⟨84831796856802278267164657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113109062475736371022886209 84831796856802278267164657)
      ·
        refine ⟨63623847642601708700373493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84831796856802278267164657 63623847642601708700373493)
        ·
          refine ⟨5964735716493910190660015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63623847642601708700373493 5964735716493910190660015)
          ·
            refine ⟨8947103574740865285990023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964735716493910190660015 8947103574740865285990023)
            ·
              refine ⟨13420655362111297928985035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947103574740865285990023 13420655362111297928985035)
              ·
                refine ⟨20130983043166946893477553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13420655362111297928985035 20130983043166946893477553)
                ·
                  refine ⟨15098237282375210170108165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20130983043166946893477553 15098237282375210170108165)
                  ·
                    refine ⟨2830919490445351906895281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15098237282375210170108165 2830919490445351906895281)
                    ·
                      refine ⟨2123189617834013930171461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830919490445351906895281 2123189617834013930171461)
                      ·
                        rfl

theorem cell23_4134897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_4134897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134897 prefixEnd_4134897 := by exact prefixLift 4134897
  have htrace : WordTrace (prefixWord ++ tailWord_4134897) baseStart_4134897 baseEnd_4134897 := by
    simpa [prefixWord, tailWord_4134897, baseEnd_4134897] using wordTrace_append hprefix tailTrace_4134897
  have hstable : (prefixWord ++ tailWord_4134897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134897).length < 2 ^ (prefixWord ++ tailWord_4134897).sum := by decide
  have hdescent : baseEnd_4134897 < baseStart_4134897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134917 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_4134917 : Nat := 118140960795 + 4134917 * 2 ^ 59
def prefixEnd_4134917 : Nat := 4983230072969 + 3 ^ 40 * 4134917 * 2
def baseEnd_4134917 : Nat := 2123199887447103851921369

theorem tailTrace_4134917 : CollatzResearch.WordTrace tailWord_4134917 prefixEnd_4134917 2123199887447103851921369 := by
  unfold tailWord_4134917
  simp only [CollatzResearch.WordTrace]
  refine ⟨150812812760909371446243005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100541875173939580964162003 150812812760909371446243005)
  ·
    refine ⟨56554804785341014292341127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150812812760909371446243005 56554804785341014292341127)
    ·
      refine ⟨84832207178011521438511691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56554804785341014292341127 84832207178011521438511691)
      ·
        refine ⟨127248310767017282157767537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84832207178011521438511691 127248310767017282157767537)
        ·
          refine ⟨95436233075262961618325653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127248310767017282157767537 95436233075262961618325653)
          ·
            refine ⟨4473573425402951325859015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95436233075262961618325653 4473573425402951325859015)
            ·
              refine ⟨6710360138104426988788523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473573425402951325859015 6710360138104426988788523)
              ·
                refine ⟨10065540207156640483182785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710360138104426988788523 10065540207156640483182785)
                ·
                  refine ⟨7549155155367480362387089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10065540207156640483182785 7549155155367480362387089)
                  ·
                    refine ⟨5661866366525610271790317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549155155367480362387089 5661866366525610271790317)
                    ·
                      refine ⟨2123199887447103851921369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661866366525610271790317 2123199887447103851921369)
                      ·
                        rfl

theorem cell23_4134917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_4134917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134917 prefixEnd_4134917 := by exact prefixLift 4134917
  have htrace : WordTrace (prefixWord ++ tailWord_4134917) baseStart_4134917 baseEnd_4134917 := by
    simpa [prefixWord, tailWord_4134917, baseEnd_4134917] using wordTrace_append hprefix tailTrace_4134917
  have hstable : (prefixWord ++ tailWord_4134917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134917).length < 2 ^ (prefixWord ++ tailWord_4134917).sum := by decide
  have hdescent : baseEnd_4134917 < baseStart_4134917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134947 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 3]
def baseStart_4134947 : Nat := 118140960795 + 4134947 * 2 ^ 59
def prefixEnd_4134947 : Nat := 4983230072969 + 3 ^ 40 * 4134947 * 2
def baseEnd_4134947 : Nat := 2123215291866738734546231

theorem tailTrace_4134947 : CollatzResearch.WordTrace tailWord_4134947 prefixEnd_4134947 2123215291866738734546231 := by
  unfold tailWord_4134947
  simp only [CollatzResearch.WordTrace]
  refine ⟨150813906950800686569835095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100542604633867124379890063 150813906950800686569835095)
  ·
    refine ⟨226220860426201029854752643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150813906950800686569835095 226220860426201029854752643)
    ·
      refine ⟨339331290639301544782128965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226220860426201029854752643 339331290639301544782128965)
      ·
        refine ⟨63624616994869039646649181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339331290639301544782128965 63624616994869039646649181)
        ·
          refine ⟨23859231373075889867493443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63624616994869039646649181 23859231373075889867493443)
          ·
            refine ⟨35788847059613834801240165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23859231373075889867493443 35788847059613834801240165)
            ·
              refine ⟨6710408823677594025232531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35788847059613834801240165 6710408823677594025232531)
              ·
                refine ⟨10065613235516391037848797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710408823677594025232531 10065613235516391037848797)
                ·
                  refine ⟨3774604963318646639193299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10065613235516391037848797 3774604963318646639193299)
                  ·
                    refine ⟨5661907444977969958789949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774604963318646639193299 5661907444977969958789949)
                    ·
                      refine ⟨2123215291866738734546231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661907444977969958789949 2123215291866738734546231)
                      ·
                        rfl

theorem cell23_4134947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_4134947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134947 prefixEnd_4134947 := by exact prefixLift 4134947
  have htrace : WordTrace (prefixWord ++ tailWord_4134947) baseStart_4134947 baseEnd_4134947 := by
    simpa [prefixWord, tailWord_4134947, baseEnd_4134947] using wordTrace_append hprefix tailTrace_4134947
  have hstable : (prefixWord ++ tailWord_4134947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134947).length < 2 ^ (prefixWord ++ tailWord_4134947).sum := by decide
  have hdescent : baseEnd_4134947 < baseStart_4134947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134970 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_4134970 : Nat := 118140960795 + 4134970 * 2 ^ 59
def prefixEnd_4134970 : Nat := 4983230072969 + 3 ^ 40 * 4134970 * 2
def baseEnd_4134970 : Nat := 2123227101921792144558625

theorem tailTrace_4134970 : CollatzResearch.WordTrace tailWord_4134970 prefixEnd_4134970 2123227101921792144558625 := by
  unfold tailWord_4134970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37703686457429340374480591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100543163886478240998614909 37703686457429340374480591)
  ·
    refine ⟨56555529686144010561720887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37703686457429340374480591 56555529686144010561720887)
    ·
      refine ⟨84833294529216015842581331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56555529686144010561720887 84833294529216015842581331)
      ·
        refine ⟨127249941793824023763871997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84833294529216015842581331 127249941793824023763871997)
        ·
          refine ⟨47718728172684008911451999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127249941793824023763871997 47718728172684008911451999)
          ·
            refine ⟨71578092259026013367177999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47718728172684008911451999 71578092259026013367177999)
            ·
              refine ⟨107367138388539020050766999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71578092259026013367177999 107367138388539020050766999)
              ·
                refine ⟨161050707582808530076150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107367138388539020050766999 161050707582808530076150499)
                ·
                  refine ⟨241576061374212795114225749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161050707582808530076150499 241576061374212795114225749)
                  ·
                    refine ⟨2830969469229056192744833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 241576061374212795114225749 2830969469229056192744833)
                    ·
                      refine ⟨2123227101921792144558625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2830969469229056192744833 2123227101921792144558625)
                      ·
                        rfl

theorem cell23_4134970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_4134970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134970 prefixEnd_4134970 := by exact prefixLift 4134970
  have htrace : WordTrace (prefixWord ++ tailWord_4134970) baseStart_4134970 baseEnd_4134970 := by
    simpa [prefixWord, tailWord_4134970, baseEnd_4134970] using wordTrace_append hprefix tailTrace_4134970
  have hstable : (prefixWord ++ tailWord_4134970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134970).length < 2 ^ (prefixWord ++ tailWord_4134970).sum := by decide
  have hdescent : baseEnd_4134970 < baseStart_4134970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134990 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4134990 : Nat := 118140960795 + 4134990 * 2 ^ 59
def prefixEnd_4134990 : Nat := 4983230072969 + 3 ^ 40 * 4134990 * 2
def baseEnd_4134990 : Nat := 2123237371534882066308533

theorem tailTrace_4134990 : CollatzResearch.WordTrace tailWord_4134990 prefixEnd_4134990 2123237371534882066308533 := by
  unfold tailWord_4134990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851934411205613114206303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100543650193096603275766949 18851934411205613114206303)
  ·
    refine ⟨28277901616808419671309455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18851934411205613114206303 28277901616808419671309455)
    ·
      refine ⟨42416852425212629506964183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28277901616808419671309455 42416852425212629506964183)
      ·
        refine ⟨63625278637818944260446275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42416852425212629506964183 63625278637818944260446275)
        ·
          refine ⟨95437917956728416390669413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63625278637818944260446275 95437917956728416390669413)
          ·
            refine ⟨17894609616886578073250515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95437917956728416390669413 17894609616886578073250515)
            ·
              refine ⟨26841914425329867109875773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17894609616886578073250515 26841914425329867109875773)
              ·
                refine ⟨10065717909498700166203415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26841914425329867109875773 10065717909498700166203415)
                ·
                  refine ⟨15098576864248050249305123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10065717909498700166203415 15098576864248050249305123)
                  ·
                    refine ⟨22647865296372075373957685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15098576864248050249305123 22647865296372075373957685)
                    ·
                      refine ⟨2123237371534882066308533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22647865296372075373957685 2123237371534882066308533)
                      ·
                        rfl

theorem cell23_4134990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4134990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134990 prefixEnd_4134990 := by exact prefixLift 4134990
  have htrace : WordTrace (prefixWord ++ tailWord_4134990) baseStart_4134990 baseEnd_4134990 := by
    simpa [prefixWord, tailWord_4134990, baseEnd_4134990] using wordTrace_append hprefix tailTrace_4134990
  have hstable : (prefixWord ++ tailWord_4134990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134990).length < 2 ^ (prefixWord ++ tailWord_4134990).sum := by decide
  have hdescent : baseEnd_4134990 < baseStart_4134990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134998 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4134998 : Nat := 118140960795 + 4134998 * 2 ^ 59
def prefixEnd_4134998 : Nat := 4983230072969 + 3 ^ 40 * 4134998 * 2
def baseEnd_4134998 : Nat := 2123241479380118035008497

theorem tailTrace_4134998 : CollatzResearch.WordTrace tailWord_4134998 prefixEnd_4134998 2123241479380118035008497 := by
  unfold tailWord_4134998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425985442100995142496353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100543844715743948186627765 9425985442100995142496353)
  ·
    refine ⟨7069489081575746356872265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9425985442100995142496353 7069489081575746356872265)
    ·
      refine ⟨5302116811181809767654199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7069489081575746356872265 5302116811181809767654199)
      ·
        refine ⟨7953175216772714651481299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302116811181809767654199 7953175216772714651481299)
        ·
          refine ⟨11929762825159071977221949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953175216772714651481299 11929762825159071977221949)
          ·
            refine ⟨4473661059434651991458231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11929762825159071977221949 4473661059434651991458231)
            ·
              refine ⟨6710491589151977987187347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473661059434651991458231 6710491589151977987187347)
              ·
                refine ⟨10065737383727966980781021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710491589151977987187347 10065737383727966980781021)
                ·
                  refine ⟨3774651518897987617792883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10065737383727966980781021 3774651518897987617792883)
                  ·
                    refine ⟨5661977278346981426689325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774651518897987617792883 5661977278346981426689325)
                    ·
                      refine ⟨2123241479380118035008497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5661977278346981426689325 2123241479380118035008497)
                      ·
                        rfl

theorem cell23_4134998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4134998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4134998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4134998 prefixEnd_4134998 := by exact prefixLift 4134998
  have htrace : WordTrace (prefixWord ++ tailWord_4134998) baseStart_4134998 baseEnd_4134998 := by
    simpa [prefixWord, tailWord_4134998, baseEnd_4134998] using wordTrace_append hprefix tailTrace_4134998
  have hstable : (prefixWord ++ tailWord_4134998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134998).length < 2 ^ (prefixWord ++ tailWord_4134998).sum := by decide
  have hdescent : baseEnd_4134998 < baseStart_4134998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135024 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_4135024 : Nat := 118140960795 + 4135024 * 2 ^ 59
def prefixEnd_4135024 : Nat := 4983230072969 + 3 ^ 40 * 4135024 * 2
def baseEnd_4135024 : Nat := 2123254829877134933283377

theorem tailTrace_4135024 : CollatzResearch.WordTrace tailWord_4135024 prefixEnd_4135024 2123254829877134933283377 := by
  unfold tailWord_4135024
  simp only [CollatzResearch.WordTrace]
  refine ⟨75408357685760864360194063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100544476914347819146925417 75408357685760864360194063)
  ·
    refine ⟨113112536528641296540291095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75408357685760864360194063 113112536528641296540291095)
    ·
      refine ⟨169668804792961944810436643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113112536528641296540291095 169668804792961944810436643)
      ·
        refine ⟨254503207189442917215654965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169668804792961944810436643 254503207189442917215654965)
        ·
          refine ⟨23859675674010273488967653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254503207189442917215654965 23859675674010273488967653)
          ·
            refine ⟨4473689188876926279181435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23859675674010273488967653 4473689188876926279181435)
            ·
              refine ⟨6710533783315389418772153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473689188876926279181435 6710533783315389418772153)
              ·
                refine ⟨5032900337486542064079115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710533783315389418772153 5032900337486542064079115)
                ·
                  refine ⟨7549350506229813096118673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032900337486542064079115 7549350506229813096118673)
                  ·
                    refine ⟨5662012879672359822089005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549350506229813096118673 5662012879672359822089005)
                    ·
                      refine ⟨2123254829877134933283377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662012879672359822089005 2123254829877134933283377)
                      ·
                        rfl

theorem cell23_4135024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_4135024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135024 prefixEnd_4135024 := by exact prefixLift 4135024
  have htrace : WordTrace (prefixWord ++ tailWord_4135024) baseStart_4135024 baseEnd_4135024 := by
    simpa [prefixWord, tailWord_4135024, baseEnd_4135024] using wordTrace_append hprefix tailTrace_4135024
  have hstable : (prefixWord ++ tailWord_4135024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135024).length < 2 ^ (prefixWord ++ tailWord_4135024).sum := by decide
  have hdescent : baseEnd_4135024 < baseStart_4135024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135037 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_4135037 : Nat := 118140960795 + 4135037 * 2 ^ 59
def prefixEnd_4135037 : Nat := 4983230072969 + 3 ^ 40 * 4135037 * 2
def baseEnd_4135037 : Nat := 2123261505125643382420817

theorem tailTrace_4135037 : CollatzResearch.WordTrace tailWord_4135037 prefixEnd_4135037 2123261505125643382420817 := by
  unfold tailWord_4135037
  simp only [CollatzResearch.WordTrace]
  refine ⟨150817189520474631940611365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100544793013649754627074243 150817189520474631940611365)
  ·
    refine ⟨28278223035088993488864631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150817189520474631940611365 28278223035088993488864631)
    ·
      refine ⟨42417334552633490233296947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278223035088993488864631 42417334552633490233296947)
      ·
        refine ⟨63626001828950235349945421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42417334552633490233296947 63626001828950235349945421)
        ·
          refine ⟨23859750685856338256229533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63626001828950235349945421 23859750685856338256229533)
          ·
            refine ⟨8947406507196126846086075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23859750685856338256229533 8947406507196126846086075)
            ·
              refine ⟨13421109760794190269129113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947406507196126846086075 13421109760794190269129113)
              ·
                refine ⟨10065832320595642701846835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13421109760794190269129113 10065832320595642701846835)
                ·
                  refine ⟨15098748480893464052770253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10065832320595642701846835 15098748480893464052770253)
                  ·
                    refine ⟨5662030680335049019788845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15098748480893464052770253 5662030680335049019788845)
                    ·
                      refine ⟨2123261505125643382420817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662030680335049019788845 2123261505125643382420817)
                      ·
                        rfl

theorem cell23_4135037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_4135037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135037 prefixEnd_4135037 := by exact prefixLift 4135037
  have htrace : WordTrace (prefixWord ++ tailWord_4135037) baseStart_4135037 baseEnd_4135037 := by
    simpa [prefixWord, tailWord_4135037, baseEnd_4135037] using wordTrace_append hprefix tailTrace_4135037
  have hstable : (prefixWord ++ tailWord_4135037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135037).length < 2 ^ (prefixWord ++ tailWord_4135037).sum := by decide
  have hdescent : baseEnd_4135037 < baseStart_4135037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135041 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_4135041 : Nat := 118140960795 + 4135041 * 2 ^ 59
def prefixEnd_4135041 : Nat := 4983230072969 + 3 ^ 40 * 4135041 * 2
def baseEnd_4135041 : Nat := 2123263559048261366770799

theorem tailTrace_4135041 : CollatzResearch.WordTrace tailWord_4135041 prefixEnd_4135041 2123263559048261366770799 := by
  unfold tailWord_4135041
  simp only [CollatzResearch.WordTrace]
  refine ⟨150817335412460140623756977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100544890274973427082504651 150817335412460140623756977)
  ·
    refine ⟨113113001559345105467817733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150817335412460140623756977 113113001559345105467817733)
    ·
      refine ⟨21208687792377207275215825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113113001559345105467817733 21208687792377207275215825)
      ·
        refine ⟨15906515844282905456411869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21208687792377207275215825 15906515844282905456411869)
        ·
          refine ⟨5964943441606089546154451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15906515844282905456411869 5964943441606089546154451)
          ·
            refine ⟨8947415162409134319231677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964943441606089546154451 8947415162409134319231677)
            ·
              refine ⟨3355280685903425369711879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947415162409134319231677 3355280685903425369711879)
              ·
                refine ⟨5032921028855138054567819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355280685903425369711879 5032921028855138054567819)
                ·
                  refine ⟨7549381543282707081851729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032921028855138054567819 7549381543282707081851729)
                  ·
                    refine ⟨5662036157462030311388797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549381543282707081851729 5662036157462030311388797)
                    ·
                      refine ⟨2123263559048261366770799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662036157462030311388797 2123263559048261366770799)
                      ·
                        rfl

theorem cell23_4135041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_4135041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135041 prefixEnd_4135041 := by exact prefixLift 4135041
  have htrace : WordTrace (prefixWord ++ tailWord_4135041) baseStart_4135041 baseEnd_4135041 := by
    simpa [prefixWord, tailWord_4135041, baseEnd_4135041] using wordTrace_append hprefix tailTrace_4135041
  have hstable : (prefixWord ++ tailWord_4135041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135041).length < 2 ^ (prefixWord ++ tailWord_4135041).sum := by decide
  have hdescent : baseEnd_4135041 < baseStart_4135041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135090 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_4135090 : Nat := 118140960795 + 4135090 * 2 ^ 59
def prefixEnd_4135090 : Nat := 4983230072969 + 3 ^ 40 * 4135090 * 2
def baseEnd_4135090 : Nat := 2123288719600331675058073

theorem tailTrace_4135090 : CollatzResearch.WordTrace tailWord_4135090 prefixEnd_4135090 2123288719600331675058073 := by
  unfold tailWord_4135090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704780647320655498072681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100546081726188414661527149 37704780647320655498072681)
  ·
    refine ⟨28278585485490491623554511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37704780647320655498072681 28278585485490491623554511)
    ·
      refine ⟨42417878228235737435331767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278585485490491623554511 42417878228235737435331767)
      ·
        refine ⟨63626817342353606152997651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42417878228235737435331767 63626817342353606152997651)
        ·
          refine ⟨95440226013530409229496477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63626817342353606152997651 95440226013530409229496477)
          ·
            refine ⟨35790084755073903461061179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95440226013530409229496477 35790084755073903461061179)
            ·
              refine ⟨53685127132610855191591769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35790084755073903461061179 53685127132610855191591769)
              ·
                refine ⟨40263845349458141393693827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53685127132610855191591769 40263845349458141393693827)
                ·
                  refine ⟨60395768024187212090540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40263845349458141393693827 60395768024187212090540741)
                  ·
                    refine ⟨11324206504535102266976389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60395768024187212090540741 11324206504535102266976389)
                    ·
                      refine ⟨2123288719600331675058073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11324206504535102266976389 2123288719600331675058073)
                      ·
                        rfl

theorem cell23_4135090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_4135090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135090 prefixEnd_4135090 := by exact prefixLift 4135090
  have htrace : WordTrace (prefixWord ++ tailWord_4135090) baseStart_4135090 baseEnd_4135090 := by
    simpa [prefixWord, tailWord_4135090, baseEnd_4135090] using wordTrace_append hprefix tailTrace_4135090
  have hstable : (prefixWord ++ tailWord_4135090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135090).length < 2 ^ (prefixWord ++ tailWord_4135090).sum := by decide
  have hdescent : baseEnd_4135090 < baseStart_4135090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135092 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4135092 : Nat := 118140960795 + 4135092 * 2 ^ 59
def prefixEnd_4135092 : Nat := 4983230072969 + 3 ^ 40 * 4135092 * 2
def baseEnd_4135092 : Nat := 2123289746561640667233065

theorem tailTrace_4135092 : CollatzResearch.WordTrace tailWord_4135092 prefixEnd_4135092 2123289746561640667233065 := by
  unfold tailWord_4135092
  simp only [CollatzResearch.WordTrace]
  refine ⟨75409597767637688166931765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100546130356850250889242353 75409597767637688166931765)
  ·
    refine ⟨7069649790716033265649853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75409597767637688166931765 7069649790716033265649853)
    ·
      refine ⟨2651118671518512474618695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7069649790716033265649853 2651118671518512474618695)
      ·
        refine ⟨3976678007277768711928043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651118671518512474618695 3976678007277768711928043)
        ·
          refine ⟨5965017010916653067892065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976678007277768711928043 5965017010916653067892065)
          ·
            refine ⟨4473762758187489800919049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965017010916653067892065 4473762758187489800919049)
            ·
              refine ⟨3355322068640617350689287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473762758187489800919049 3355322068640617350689287)
              ·
                refine ⟨5032983102960926026033931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355322068640617350689287 5032983102960926026033931)
                ·
                  refine ⟨7549474654441389039050897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032983102960926026033931 7549474654441389039050897)
                  ·
                    refine ⟨5662105990831041779288173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549474654441389039050897 5662105990831041779288173)
                    ·
                      refine ⟨2123289746561640667233065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662105990831041779288173 2123289746561640667233065)
                      ·
                        rfl

theorem cell23_4135092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4135092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135092 prefixEnd_4135092 := by exact prefixLift 4135092
  have htrace : WordTrace (prefixWord ++ tailWord_4135092) baseStart_4135092 baseEnd_4135092 := by
    simpa [prefixWord, tailWord_4135092, baseEnd_4135092] using wordTrace_append hprefix tailTrace_4135092
  have hstable : (prefixWord ++ tailWord_4135092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135092).length < 2 ^ (prefixWord ++ tailWord_4135092).sum := by decide
  have hdescent : baseEnd_4135092 < baseStart_4135092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135105 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4135105 : Nat := 118140960795 + 4135105 * 2 ^ 59
def prefixEnd_4135105 : Nat := 4983230072969 + 3 ^ 40 * 4135105 * 2
def baseEnd_4135105 : Nat := 2123296421810149116370505

theorem tailTrace_4135105 : CollatzResearch.WordTrace tailWord_4135105 prefixEnd_4135105 2123296421810149116370505 := by
  unfold tailWord_4135105
  simp only [CollatzResearch.WordTrace]
  refine ⟨150819669684228279554086769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100546446456152186369391179 150819669684228279554086769)
  ·
    refine ⟨113114752263171209665565077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150819669684228279554086769 113114752263171209665565077)
    ·
      refine ⟨5302254012336150453073363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113114752263171209665565077 5302254012336150453073363)
      ·
        refine ⟨7953381018504225679610045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302254012336150453073363 7953381018504225679610045)
        ·
          refine ⟨2982517881939084629853767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7953381018504225679610045 2982517881939084629853767)
          ·
            refine ⟨4473776822908626944780651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982517881939084629853767 4473776822908626944780651)
            ·
              refine ⟨6710665234362940417170977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473776822908626944780651 6710665234362940417170977)
              ·
                refine ⟨5032998925772205312878233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710665234362940417170977 5032998925772205312878233)
                ·
                  refine ⟨3774749194329153984658675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032998925772205312878233 3774749194329153984658675)
                  ·
                    refine ⟨5662123791493730976988013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774749194329153984658675 5662123791493730976988013)
                    ·
                      refine ⟨2123296421810149116370505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662123791493730976988013 2123296421810149116370505)
                      ·
                        rfl

theorem cell23_4135105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4135105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135105 prefixEnd_4135105 := by exact prefixLift 4135105
  have htrace : WordTrace (prefixWord ++ tailWord_4135105) baseStart_4135105 baseEnd_4135105 := by
    simpa [prefixWord, tailWord_4135105, baseEnd_4135105] using wordTrace_append hprefix tailTrace_4135105
  have hstable : (prefixWord ++ tailWord_4135105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135105).length < 2 ^ (prefixWord ++ tailWord_4135105).sum := by decide
  have hdescent : baseEnd_4135105 < baseStart_4135105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135128 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_4135128 : Nat := 118140960795 + 4135128 * 2 ^ 59
def prefixEnd_4135128 : Nat := 4983230072969 + 3 ^ 40 * 4135128 * 2
def baseEnd_4135128 : Nat := 2123308231865202526382899

theorem tailTrace_4135128 : CollatzResearch.WordTrace tailWord_4135128 prefixEnd_4135128 2123308231865202526382899 := by
  unfold tailWord_4135128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75410254281572477241087019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100547005708763302988116025 75410254281572477241087019)
  ·
    refine ⟨113115381422358715861630529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75410254281572477241087019 113115381422358715861630529)
    ·
      refine ⟨84836536066769036896222897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113115381422358715861630529 84836536066769036896222897)
      ·
        refine ⟨63627402050076777672167173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84836536066769036896222897 63627402050076777672167173)
        ·
          refine ⟨11930137884389395813531345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63627402050076777672167173 11930137884389395813531345)
          ·
            refine ⟨8947603413292046860148509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11930137884389395813531345 8947603413292046860148509)
            ·
              refine ⟨3355351279984517572555691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947603413292046860148509 3355351279984517572555691)
              ·
                refine ⟨5033026919976776358833537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355351279984517572555691 5033026919976776358833537)
                ·
                  refine ⟨3774770189982582269125153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033026919976776358833537 3774770189982582269125153)
                  ·
                    refine ⟨2831077642486936701843865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3774770189982582269125153 2831077642486936701843865)
                    ·
                      refine ⟨2123308231865202526382899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831077642486936701843865 2123308231865202526382899)
                      ·
                        rfl

theorem cell23_4135128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_4135128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135128 prefixEnd_4135128 := by exact prefixLift 4135128
  have htrace : WordTrace (prefixWord ++ tailWord_4135128) baseStart_4135128 baseEnd_4135128 := by
    simpa [prefixWord, tailWord_4135128, baseEnd_4135128] using wordTrace_append hprefix tailTrace_4135128
  have hstable : (prefixWord ++ tailWord_4135128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135128).length < 2 ^ (prefixWord ++ tailWord_4135128).sum := by decide
  have hdescent : baseEnd_4135128 < baseStart_4135128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135130 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_4135130 : Nat := 118140960795 + 4135130 * 2 ^ 59
def prefixEnd_4135130 : Nat := 4983230072969 + 3 ^ 40 * 4135130 * 2
def baseEnd_4135130 : Nat := 707769752942170506185963

theorem tailTrace_4135130 : CollatzResearch.WordTrace tailWord_4135130 prefixEnd_4135130 707769752942170506185963 := by
  unfold tailWord_4135130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37705145377284427205936711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100547054339425139215831229 37705145377284427205936711)
  ·
    refine ⟨56557718065926640808905067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37705145377284427205936711 56557718065926640808905067)
    ·
      refine ⟨84836577098889961213357601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56557718065926640808905067 84836577098889961213357601)
      ·
        refine ⟨63627432824167470910018201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84836577098889961213357601 63627432824167470910018201)
        ·
          refine ⟨47720574618125603182513651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63627432824167470910018201 47720574618125603182513651)
          ·
            refine ⟨71580861927188404773770477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47720574618125603182513651 71580861927188404773770477)
            ·
              refine ⟨26842823222695651790163929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71580861927188404773770477 26842823222695651790163929)
              ·
                refine ⟨20132117417021738842622947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26842823222695651790163929 20132117417021738842622947)
                ·
                  refine ⟨30198176125532608263934421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20132117417021738842622947 30198176125532608263934421)
                  ·
                    refine ⟨707769752942170506185963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30198176125532608263934421 707769752942170506185963)
                    ·
                      rfl

theorem cell23_4135130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_4135130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135130 prefixEnd_4135130 := by exact prefixLift 4135130
  have htrace : WordTrace (prefixWord ++ tailWord_4135130) baseStart_4135130 baseEnd_4135130 := by
    simpa [prefixWord, tailWord_4135130, baseEnd_4135130] using wordTrace_append hprefix tailTrace_4135130
  have hstable : (prefixWord ++ tailWord_4135130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135130).length < 2 ^ (prefixWord ++ tailWord_4135130).sum := by decide
  have hdescent : baseEnd_4135130 < baseStart_4135130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135140 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_4135140 : Nat := 118140960795 + 4135140 * 2 ^ 59
def prefixEnd_4135140 : Nat := 4983230072969 + 3 ^ 40 * 4135140 * 2
def baseEnd_4135140 : Nat := 2123314393633056479432843

theorem tailTrace_4135140 : CollatzResearch.WordTrace tailWord_4135140 prefixEnd_4135140 2123314393633056479432843 := by
  unfold tailWord_4135140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75410473119550740265805437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100547297492734320354407249 75410473119550740265805437)
  ·
    refine ⟨28278927419831527599677039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75410473119550740265805437 28278927419831527599677039)
    ·
      refine ⟨42418391129747291399515559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278927419831527599677039 42418391129747291399515559)
      ·
        refine ⟨63627586694620937099273339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42418391129747291399515559 63627586694620937099273339)
        ·
          refine ⟨95441380041931405648910009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63627586694620937099273339 95441380041931405648910009)
          ·
            refine ⟨71581035031448554236682507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95441380041931405648910009 71581035031448554236682507)
            ·
              refine ⟨107371552547172831355023761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71581035031448554236682507 107371552547172831355023761)
              ·
                refine ⟨80528664410379623516267821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107371552547172831355023761 80528664410379623516267821)
                ·
                  refine ⟨30198249153892358818600433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80528664410379623516267821 30198249153892358818600433)
                  ·
                    refine ⟨22648686865419269113950325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30198249153892358818600433 22648686865419269113950325)
                    ·
                      refine ⟨2123314393633056479432843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22648686865419269113950325 2123314393633056479432843)
                      ·
                        rfl

theorem cell23_4135140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_4135140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135140 prefixEnd_4135140 := by exact prefixLift 4135140
  have htrace : WordTrace (prefixWord ++ tailWord_4135140) baseStart_4135140 baseEnd_4135140 := by
    simpa [prefixWord, tailWord_4135140, baseEnd_4135140] using wordTrace_append hprefix tailTrace_4135140
  have hstable : (prefixWord ++ tailWord_4135140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135140).length < 2 ^ (prefixWord ++ tailWord_4135140).sum := by decide
  have hdescent : baseEnd_4135140 < baseStart_4135140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135167 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_4135167 : Nat := 118140960795 + 4135167 * 2 ^ 59
def prefixEnd_4135167 : Nat := 4983230072969 + 3 ^ 40 * 4135167 * 2
def baseEnd_4135167 : Nat := 2123328257610727873795219

theorem tailTrace_4135167 : CollatzResearch.WordTrace tailWord_4135167 prefixEnd_4135167 2123328257610727873795219 := by
  unfold tailWord_4135167
  simp only [CollatzResearch.WordTrace]
  refine ⟨150821931010003664142843755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100547954006669109428562503 150821931010003664142843755)
  ·
    refine ⟨226232896515005496214265633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150821931010003664142843755 226232896515005496214265633)
    ·
      refine ⟨169674672386254122160699225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226232896515005496214265633 169674672386254122160699225)
      ·
        refine ⟨127256004289690591620524419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169674672386254122160699225 127256004289690591620524419)
        ·
          refine ⟨190884006434535887430786629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127256004289690591620524419 190884006434535887430786629)
          ·
            refine ⟨35790751206475478893272493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190884006434535887430786629 35790751206475478893272493)
            ·
              refine ⟨13421531702428304584977185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35790751206475478893272493 13421531702428304584977185)
              ·
                refine ⟨10066148776821228438732889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13421531702428304584977185 10066148776821228438732889)
                ·
                  refine ⟨7549611582615921329049667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066148776821228438732889 7549611582615921329049667)
                  ·
                    refine ⟨11324417373923881993574501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549611582615921329049667 11324417373923881993574501)
                    ·
                      refine ⟨2123328257610727873795219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11324417373923881993574501 2123328257610727873795219)
                      ·
                        rfl

theorem cell23_4135167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_4135167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135167 prefixEnd_4135167 := by exact prefixLift 4135167
  have htrace : WordTrace (prefixWord ++ tailWord_4135167) baseStart_4135167 baseEnd_4135167 := by
    simpa [prefixWord, tailWord_4135167, baseEnd_4135167] using wordTrace_append hprefix tailTrace_4135167
  have hstable : (prefixWord ++ tailWord_4135167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135167).length < 2 ^ (prefixWord ++ tailWord_4135167).sum := by decide
  have hdescent : baseEnd_4135167 < baseStart_4135167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135204 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_4135204 : Nat := 118140960795 + 4135204 * 2 ^ 59
def prefixEnd_4135204 : Nat := 4983230072969 + 3 ^ 40 * 4135204 * 2
def baseEnd_4135204 : Nat := 2123347256394944229032549

theorem tailTrace_4135204 : CollatzResearch.WordTrace tailWord_4135204 prefixEnd_4135204 2123347256394944229032549 := by
  unfold tailWord_4135204
  simp only [CollatzResearch.WordTrace]
  refine ⟨75411640255434809730970333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100548853673913079641293777 75411640255434809730970333)
  ·
    refine ⟨28279365095788053649113875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75411640255434809730970333 28279365095788053649113875)
    ·
      refine ⟨42419047643682080473670813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28279365095788053649113875 42419047643682080473670813)
      ·
        refine ⟨15907142866380780177626555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42419047643682080473670813 15907142866380780177626555)
        ·
          refine ⟨23860714299571170266439833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907142866380780177626555 23860714299571170266439833)
          ·
            refine ⟨17895535724678377699829875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23860714299571170266439833 17895535724678377699829875)
            ·
              refine ⟨26843303587017566549744813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895535724678377699829875 26843303587017566549744813)
              ·
                refine ⟨10066238845131587456154305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26843303587017566549744813 10066238845131587456154305)
                ·
                  refine ⟨7549679133848690592115729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066238845131587456154305 7549679133848690592115729)
                  ·
                    refine ⟨5662259350386517944086797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549679133848690592115729 5662259350386517944086797)
                    ·
                      refine ⟨2123347256394944229032549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662259350386517944086797 2123347256394944229032549)
                      ·
                        rfl

theorem cell23_4135204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_4135204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135204 prefixEnd_4135204 := by exact prefixLift 4135204
  have htrace : WordTrace (prefixWord ++ tailWord_4135204) baseStart_4135204 baseEnd_4135204 := by
    simpa [prefixWord, tailWord_4135204, baseEnd_4135204] using wordTrace_append hprefix tailTrace_4135204
  have hstable : (prefixWord ++ tailWord_4135204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135204).length < 2 ^ (prefixWord ++ tailWord_4135204).sum := by decide
  have hdescent : baseEnd_4135204 < baseStart_4135204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135244 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4135244 : Nat := 118140960795 + 4135244 * 2 ^ 59
def prefixEnd_4135244 : Nat := 4983230072969 + 3 ^ 40 * 4135244 * 2
def baseEnd_4135244 : Nat := 2123367795621124072532365

theorem tailTrace_4135244 : CollatzResearch.WordTrace tailWord_4135244 prefixEnd_4135244 2123367795621124072532365 := by
  unfold tailWord_4135244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75412369715362353146698393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100549826287149804195597857 75412369715362353146698393)
  ·
    refine ⟨56559277286521764860023795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75412369715362353146698393 56559277286521764860023795)
    ·
      refine ⟨84838915929782647290035693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56559277286521764860023795 84838915929782647290035693)
      ·
        refine ⟨31814593473668492733763385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84838915929782647290035693 31814593473668492733763385)
        ·
          refine ⟨23860945105251369550322539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31814593473668492733763385 23860945105251369550322539)
          ·
            refine ⟨35791417657877054325483809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23860945105251369550322539 35791417657877054325483809)
            ·
              refine ⟨26843563243407790744112857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35791417657877054325483809 26843563243407790744112857)
              ·
                refine ⟨20132672432555843058084643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26843563243407790744112857 20132672432555843058084643)
                ·
                  refine ⟨30199008648833764587126965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20132672432555843058084643 30199008648833764587126965)
                  ·
                    refine ⟨2831157060828165430043153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30199008648833764587126965 2831157060828165430043153)
                    ·
                      refine ⟨2123367795621124072532365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831157060828165430043153 2123367795621124072532365)
                      ·
                        rfl

theorem cell23_4135244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4135244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135244 prefixEnd_4135244 := by exact prefixLift 4135244
  have htrace : WordTrace (prefixWord ++ tailWord_4135244) baseStart_4135244 baseEnd_4135244 := by
    simpa [prefixWord, tailWord_4135244, baseEnd_4135244] using wordTrace_append hprefix tailTrace_4135244
  have hstable : (prefixWord ++ tailWord_4135244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135244).length < 2 ^ (prefixWord ++ tailWord_4135244).sum := by decide
  have hdescent : baseEnd_4135244 < baseStart_4135244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135267 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 1, 6]
def baseStart_4135267 : Nat := 118140960795 + 4135267 * 2 ^ 59
def prefixEnd_4135267 : Nat := 4983230072969 + 3 ^ 40 * 4135267 * 2
def baseEnd_4135267 : Nat := 707793201892059160848253

theorem tailTrace_4135267 : CollatzResearch.WordTrace tailWord_4135267 prefixEnd_4135267 707793201892059160848253 := by
  unfold tailWord_4135267
  simp only [CollatzResearch.WordTrace]
  refine ⟨150825578309641381221484055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100550385539760920814322703 150825578309641381221484055)
  ·
    refine ⟨226238367464462071832226083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150825578309641381221484055 226238367464462071832226083)
    ·
      refine ⟨339357551196693107748339125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226238367464462071832226083 339357551196693107748339125)
      ·
        refine ⟨31814770424689978851406793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339357551196693107748339125 31814770424689978851406793)
        ·
          refine ⟨23861077818517484138555095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31814770424689978851406793 23861077818517484138555095)
          ·
            refine ⟨35791616727776226207832643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23861077818517484138555095 35791616727776226207832643)
            ·
              refine ⟨53687425091664339311748965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35791616727776226207832643 53687425091664339311748965)
              ·
                refine ⟨10066392204687063620952931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53687425091664339311748965 10066392204687063620952931)
                ·
                  refine ⟨15099588307030595431429397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066392204687063620952931 15099588307030595431429397)
                  ·
                    refine ⟨707793201892059160848253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15099588307030595431429397 707793201892059160848253)
                    ·
                      rfl

theorem cell23_4135267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 6].length) (baseStart_4135267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135267 prefixEnd_4135267 := by exact prefixLift 4135267
  have htrace : WordTrace (prefixWord ++ tailWord_4135267) baseStart_4135267 baseEnd_4135267 := by
    simpa [prefixWord, tailWord_4135267, baseEnd_4135267] using wordTrace_append hprefix tailTrace_4135267
  have hstable : (prefixWord ++ tailWord_4135267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135267).length < 2 ^ (prefixWord ++ tailWord_4135267).sum := by decide
  have hdescent : baseEnd_4135267 < baseStart_4135267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135268 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_4135268 : Nat := 118140960795 + 4135268 * 2 ^ 59
def prefixEnd_4135268 : Nat := 4983230072969 + 3 ^ 40 * 4135268 * 2
def baseEnd_4135268 : Nat := 2123380119156831978632255

theorem tailTrace_4135268 : CollatzResearch.WordTrace tailWord_4135268 prefixEnd_4135268 2123380119156831978632255 := by
  unfold tailWord_4135268
  simp only [CollatzResearch.WordTrace]
  refine ⟨75412807391318879196135229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100550409855091838928180305 75412807391318879196135229)
  ·
    refine ⟨28279802771744579698550711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75412807391318879196135229 28279802771744579698550711)
    ·
      refine ⟨42419704157616869547826067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28279802771744579698550711 42419704157616869547826067)
      ·
        refine ⟨63629556236425304321739101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42419704157616869547826067 63629556236425304321739101)
        ·
          refine ⟨23861083588659489120652163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63629556236425304321739101 23861083588659489120652163)
          ·
            refine ⟨35791625382989233680978245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23861083588659489120652163 35791625382989233680978245)
            ·
              refine ⟨6710929759310481315183421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35791625382989233680978245 6710929759310481315183421)
              ·
                refine ⟨2516598659741430493193783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6710929759310481315183421 2516598659741430493193783)
                ·
                  refine ⟨3774897989612145739790675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516598659741430493193783 3774897989612145739790675)
                  ·
                    refine ⟨5662346984418218609686013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774897989612145739790675 5662346984418218609686013)
                    ·
                      refine ⟨2123380119156831978632255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662346984418218609686013 2123380119156831978632255)
                      ·
                        rfl

theorem cell23_4135268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_4135268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135268 prefixEnd_4135268 := by exact prefixLift 4135268
  have htrace : WordTrace (prefixWord ++ tailWord_4135268) baseStart_4135268 baseEnd_4135268 := by
    simpa [prefixWord, tailWord_4135268, baseEnd_4135268] using wordTrace_append hprefix tailTrace_4135268
  have hstable : (prefixWord ++ tailWord_4135268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135268).length < 2 ^ (prefixWord ++ tailWord_4135268).sum := by decide
  have hdescent : baseEnd_4135268 < baseStart_4135268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135271 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 1, 5]
def baseStart_4135271 : Nat := 118140960795 + 4135271 * 2 ^ 59
def prefixEnd_4135271 : Nat := 4983230072969 + 3 ^ 40 * 4135271 * 2
def baseEnd_4135271 : Nat := 707793886532931822298247

theorem tailTrace_4135271 : CollatzResearch.WordTrace tailWord_4135271 prefixEnd_4135271 707793886532931822298247 := by
  unfold tailWord_4135271
  simp only [CollatzResearch.WordTrace]
  refine ⟨150825724201626889904629667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100550482801084593269753111 150825724201626889904629667)
  ·
    refine ⟨226238586302440334856944501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150825724201626889904629667 226238586302440334856944501)
    ·
      refine ⟨21209867465853781392838547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226238586302440334856944501 21209867465853781392838547)
      ·
        refine ⟨31814801198780672089257821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21209867465853781392838547 31814801198780672089257821)
        ·
          refine ⟨11930550449542752033471683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31814801198780672089257821 11930550449542752033471683)
          ·
            refine ⟨17895825674314128050207525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930550449542752033471683 17895825674314128050207525)
            ·
              refine ⟨3355467313933899009413911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17895825674314128050207525 3355467313933899009413911)
              ·
                refine ⟨5033200970900848514120867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355467313933899009413911 5033200970900848514120867)
                ·
                  refine ⟨7549801456351272771181301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033200970900848514120867 7549801456351272771181301)
                  ·
                    refine ⟨707793886532931822298247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7549801456351272771181301 707793886532931822298247)
                    ·
                      rfl

theorem cell23_4135271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_4135271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135271 prefixEnd_4135271 := by exact prefixLift 4135271
  have htrace : WordTrace (prefixWord ++ tailWord_4135271) baseStart_4135271 baseEnd_4135271 := by
    simpa [prefixWord, tailWord_4135271, baseEnd_4135271] using wordTrace_append hprefix tailTrace_4135271
  have hstable : (prefixWord ++ tailWord_4135271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135271).length < 2 ^ (prefixWord ++ tailWord_4135271).sum := by decide
  have hdescent : baseEnd_4135271 < baseStart_4135271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135291 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 3, 2, 2]
def baseStart_4135291 : Nat := 118140960795 + 4135291 * 2 ^ 59
def prefixEnd_4135291 : Nat := 4983230072969 + 3 ^ 40 * 4135291 * 2
def baseEnd_4135291 : Nat := 2123391929211885388644649

theorem tailTrace_4135291 : CollatzResearch.WordTrace tailWord_4135291 prefixEnd_4135291 2123391929211885388644649 := by
  unfold tailWord_4135291
  simp only [CollatzResearch.WordTrace]
  refine ⟨150826453661554433320357727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100550969107702955546905151 150826453661554433320357727)
  ·
    refine ⟨226239680492331649980536591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150826453661554433320357727 226239680492331649980536591)
    ·
      refine ⟨339359520738497474970804887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226239680492331649980536591 339359520738497474970804887)
      ·
        refine ⟨509039281107746212456207331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339359520738497474970804887 509039281107746212456207331)
        ·
          refine ⟨763558921661619318684310997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509039281107746212456207331 763558921661619318684310997)
          ·
            refine ⟨17895912226444202781663539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 763558921661619318684310997 17895912226444202781663539)
            ·
              refine ⟨26843868339666304172495309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895912226444202781663539 26843868339666304172495309)
              ·
                refine ⟨10066450627374864064685741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26843868339666304172495309 10066450627374864064685741)
                ·
                  refine ⟨3774918985265574024257153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10066450627374864064685741 3774918985265574024257153)
                  ·
                    refine ⟨2831189238949180518192865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3774918985265574024257153 2831189238949180518192865)
                    ·
                      refine ⟨2123391929211885388644649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831189238949180518192865 2123391929211885388644649)
                      ·
                        rfl

theorem cell23_4135291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2, 2].length) (baseStart_4135291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135291 prefixEnd_4135291 := by exact prefixLift 4135291
  have htrace : WordTrace (prefixWord ++ tailWord_4135291) baseStart_4135291 baseEnd_4135291 := by
    simpa [prefixWord, tailWord_4135291, baseEnd_4135291] using wordTrace_append hprefix tailTrace_4135291
  have hstable : (prefixWord ++ tailWord_4135291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135291).length < 2 ^ (prefixWord ++ tailWord_4135291).sum := by decide
  have hdescent : baseEnd_4135291 < baseStart_4135291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135348 : List Nat := [2, 5, 2, 2, 1, 1, 2, 8]
def baseStart_4135348 : Nat := 118140960795 + 4135348 * 2 ^ 59
def prefixEnd_4135348 : Nat := 4983230072969 + 3 ^ 40 * 4135348 * 2
def baseEnd_4135348 : Nat := 78645229541081172801181

theorem tailTrace_4135348 : CollatzResearch.WordTrace tailWord_4135348 prefixEnd_4135348 78645229541081172801181 := by
  unfold tailWord_4135348
  simp only [CollatzResearch.WordTrace]
  refine ⟨75414266311173966027591349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100552355081565288036788465 75414266311173966027591349)
  ·
    refine ⟨7070087466672559315086689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75414266311173966027591349 7070087466672559315086689)
    ·
      refine ⟨5302565600004419486315017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070087466672559315086689 5302565600004419486315017)
      ·
        refine ⟨3976924200003314614736263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5302565600004419486315017 3976924200003314614736263)
        ·
          refine ⟨5965386300004971922104395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976924200003314614736263 5965386300004971922104395)
          ·
            refine ⟨8948079450007457883156593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965386300004971922104395 8948079450007457883156593)
            ·
              refine ⟨6711059587505593412367445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948079450007457883156593 6711059587505593412367445)
              ·
                refine ⟨78645229541081172801181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6711059587505593412367445 78645229541081172801181)
                ·
                  rfl

theorem cell23_4135348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 8].length) (baseStart_4135348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135348 prefixEnd_4135348 := by exact prefixLift 4135348
  have htrace : WordTrace (prefixWord ++ tailWord_4135348) baseStart_4135348 baseEnd_4135348 := by
    simpa [prefixWord, tailWord_4135348, baseEnd_4135348] using wordTrace_append hprefix tailTrace_4135348
  have hstable : (prefixWord ++ tailWord_4135348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135348).length < 2 ^ (prefixWord ++ tailWord_4135348).sum := by decide
  have hdescent : baseEnd_4135348 < baseStart_4135348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135368 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_4135368 : Nat := 118140960795 + 4135368 * 2 ^ 59
def prefixEnd_4135368 : Nat := 4983230072969 + 3 ^ 40 * 4135368 * 2
def baseEnd_4135368 : Nat := 2123431467222281587381795

theorem tailTrace_4135368 : CollatzResearch.WordTrace tailWord_4135368 prefixEnd_4135368 2123431467222281587381795 := by
  unfold tailWord_4135368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75414631041137737735455379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100552841388183650313940505 75414631041137737735455379)
  ·
    refine ⟨113121946561706606603183069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75414631041137737735455379 113121946561706606603183069)
    ·
      refine ⟨42420729960639977476193651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113121946561706606603183069 42420729960639977476193651)
      ·
        refine ⟨63631094940959966214290477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42420729960639977476193651 63631094940959966214290477)
        ·
          refine ⟨23861660602859987330358929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63631094940959966214290477 23861660602859987330358929)
          ·
            refine ⟨17896245452144990497769197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23861660602859987330358929 17896245452144990497769197)
            ·
              refine ⟨6711092044554371436663449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17896245452144990497769197 6711092044554371436663449)
              ·
                refine ⟨5033319033415778577497587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711092044554371436663449 5033319033415778577497587)
                ·
                  refine ⟨7549978550123667866246381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033319033415778577497587 7549978550123667866246381)
                  ·
                    refine ⟨2831241956296375449842393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7549978550123667866246381 2831241956296375449842393)
                    ·
                      refine ⟨2123431467222281587381795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831241956296375449842393 2123431467222281587381795)
                      ·
                        rfl

theorem cell23_4135368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_4135368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135368 prefixEnd_4135368 := by exact prefixLift 4135368
  have htrace : WordTrace (prefixWord ++ tailWord_4135368) baseStart_4135368 baseEnd_4135368 := by
    simpa [prefixWord, tailWord_4135368, baseEnd_4135368] using wordTrace_append hprefix tailTrace_4135368
  have hstable : (prefixWord ++ tailWord_4135368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135368).length < 2 ^ (prefixWord ++ tailWord_4135368).sum := by decide
  have hdescent : baseEnd_4135368 < baseStart_4135368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135381 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4135381 : Nat := 118140960795 + 4135381 * 2 ^ 59
def prefixEnd_4135381 : Nat := 4983230072969 + 3 ^ 40 * 4135381 * 2
def baseEnd_4135381 : Nat := 2123438142470790036519235

theorem tailTrace_4135381 : CollatzResearch.WordTrace tailWord_4135381 prefixEnd_4135381 2123438142470790036519235 := by
  unfold tailWord_4135381
  simp only [CollatzResearch.WordTrace]
  refine ⟨150829736231228378691133997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100553157487485585794089331 150829736231228378691133997)
  ·
    refine ⟨56561151086710642009175249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150829736231228378691133997 56561151086710642009175249)
    ·
      refine ⟨42420863315032981506881437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56561151086710642009175249 42420863315032981506881437)
      ·
        refine ⟨15907823743137368065080539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42420863315032981506881437 15907823743137368065080539)
        ·
          refine ⟨23861735614706052097620809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907823743137368065080539 23861735614706052097620809)
          ·
            refine ⟨17896301711029539073215607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23861735614706052097620809 17896301711029539073215607)
            ·
              refine ⟨26844452566544308609823411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17896301711029539073215607 26844452566544308609823411)
              ·
                refine ⟨40266678849816462914735117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26844452566544308609823411 40266678849816462914735117)
                ·
                  refine ⟨15100004568681173593025669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40266678849816462914735117 15100004568681173593025669)
                  ·
                    refine ⟨2831250856627720048692313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15100004568681173593025669 2831250856627720048692313)
                    ·
                      refine ⟨2123438142470790036519235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831250856627720048692313 2123438142470790036519235)
                      ·
                        rfl

theorem cell23_4135381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4135381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135381 prefixEnd_4135381 := by exact prefixLift 4135381
  have htrace : WordTrace (prefixWord ++ tailWord_4135381) baseStart_4135381 baseEnd_4135381 := by
    simpa [prefixWord, tailWord_4135381, baseEnd_4135381] using wordTrace_append hprefix tailTrace_4135381
  have hstable : (prefixWord ++ tailWord_4135381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135381).length < 2 ^ (prefixWord ++ tailWord_4135381).sum := by decide
  have hdescent : baseEnd_4135381 < baseStart_4135381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135407 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_4135407 : Nat := 118140960795 + 4135407 * 2 ^ 59
def prefixEnd_4135407 : Nat := 4983230072969 + 3 ^ 40 * 4135407 * 2
def baseEnd_4135407 : Nat := 2123451492967806934794115

theorem tailTrace_4135407 : CollatzResearch.WordTrace tailWord_4135407 prefixEnd_4135407 2123451492967806934794115 := by
  unfold tailWord_4135407
  simp only [CollatzResearch.WordTrace]
  refine ⟨150830684529134185131580475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100553789686089456754386983 150830684529134185131580475)
  ·
    refine ⟨226246026793701277697370713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150830684529134185131580475 226246026793701277697370713)
    ·
      refine ⟨169684520095275958273028035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226246026793701277697370713 169684520095275958273028035)
      ·
        refine ⟨254526780142913937409542053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169684520095275958273028035 254526780142913937409542053)
        ·
          refine ⟨47723771276796363264289135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254526780142913937409542053 47723771276796363264289135)
          ·
            refine ⟨71585656915194544896433703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47723771276796363264289135 71585656915194544896433703)
            ·
              refine ⟨107378485372791817344650555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71585656915194544896433703 107378485372791817344650555)
              ·
                refine ⟨161067728059187726016975833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107378485372791817344650555 161067728059187726016975833)
                ·
                  refine ⟨120800796044390794512731875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161067728059187726016975833 120800796044390794512731875)
                  ·
                    refine ⟨181201194066586191769097813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120800796044390794512731875 181201194066586191769097813)
                    ·
                      refine ⟨2123451492967806934794115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 181201194066586191769097813 2123451492967806934794115)
                      ·
                        rfl

theorem cell23_4135407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_4135407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135407 prefixEnd_4135407 := by exact prefixLift 4135407
  have htrace : WordTrace (prefixWord ++ tailWord_4135407) baseStart_4135407 baseEnd_4135407 := by
    simpa [prefixWord, tailWord_4135407, baseEnd_4135407] using wordTrace_append hprefix tailTrace_4135407
  have hstable : (prefixWord ++ tailWord_4135407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135407).length < 2 ^ (prefixWord ++ tailWord_4135407).sum := by decide
  have hdescent : baseEnd_4135407 < baseStart_4135407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135434 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_4135434 : Nat := 118140960795 + 4135434 * 2 ^ 59
def prefixEnd_4135434 : Nat := 4983230072969 + 3 ^ 40 * 4135434 * 2
def baseEnd_4135434 : Nat := 707821785648492776385497

theorem tailTrace_4135434 : CollatzResearch.WordTrace tailWord_4135434 prefixEnd_4135434 707821785648492776385497 := by
  unfold tailWord_4135434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707917325009092185703339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100554446200024245828542237 37707917325009092185703339)
  ·
    refine ⟨56561875987513638278555009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37707917325009092185703339 56561875987513638278555009)
    ·
      refine ⟨42421406990635228708916257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56561875987513638278555009 42421406990635228708916257)
      ·
        refine ⟨31816055242976421531687193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42421406990635228708916257 31816055242976421531687193)
        ·
          refine ⟨23862041432232316148765395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31816055242976421531687193 23862041432232316148765395)
          ·
            refine ⟨35793062148348474223148093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23862041432232316148765395 35793062148348474223148093)
            ·
              refine ⟨13422398305630677833680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35793062148348474223148093 13422398305630677833680535)
              ·
                refine ⟨20133597458446016750520803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13422398305630677833680535 20133597458446016750520803)
                ·
                  refine ⟨30200396187669025125781205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20133597458446016750520803 30200396187669025125781205)
                  ·
                    refine ⟨707821785648492776385497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30200396187669025125781205 707821785648492776385497)
                    ·
                      rfl

theorem cell23_4135434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_4135434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135434 prefixEnd_4135434 := by exact prefixLift 4135434
  have htrace : WordTrace (prefixWord ++ tailWord_4135434) baseStart_4135434 baseEnd_4135434 := by
    simpa [prefixWord, tailWord_4135434, baseEnd_4135434] using wordTrace_append hprefix tailTrace_4135434
  have hstable : (prefixWord ++ tailWord_4135434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135434).length < 2 ^ (prefixWord ++ tailWord_4135434).sum := by decide
  have hdescent : baseEnd_4135434 < baseStart_4135434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135438 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_4135438 : Nat := 118140960795 + 4135438 * 2 ^ 59
def prefixEnd_4135438 : Nat := 4983230072969 + 3 ^ 40 * 4135438 * 2
def baseEnd_4135438 : Nat := 235940823429788479278497

theorem tailTrace_4135438 : CollatzResearch.WordTrace tailWord_4135438 prefixEnd_4135438 235940823429788479278497 := by
  unfold tailWord_4135438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853976899002734678244871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100554543461347918283972645 18853976899002734678244871)
  ·
    refine ⟨28280965348504102017367307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18853976899002734678244871 28280965348504102017367307)
    ·
      refine ⟨42421448022756153026050961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28280965348504102017367307 42421448022756153026050961)
      ·
        refine ⟨31816086017067114769538221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42421448022756153026050961 31816086017067114769538221)
        ·
          refine ⟨11931032256400168038576833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31816086017067114769538221 11931032256400168038576833)
          ·
            refine ⟨8948274192300126028932625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11931032256400168038576833 8948274192300126028932625)
            ·
              refine ⟨6711205644225094521699469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948274192300126028932625 6711205644225094521699469)
              ·
                refine ⟨2516702116584410445637301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6711205644225094521699469 2516702116584410445637301)
                ·
                  refine ⟨235940823429788479278497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2516702116584410445637301 235940823429788479278497)
                  ·
                    rfl

theorem cell23_4135438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_4135438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135438 prefixEnd_4135438 := by exact prefixLift 4135438
  have htrace : WordTrace (prefixWord ++ tailWord_4135438) baseStart_4135438 baseEnd_4135438 := by
    simpa [prefixWord, tailWord_4135438, baseEnd_4135438] using wordTrace_append hprefix tailTrace_4135438
  have hstable : (prefixWord ++ tailWord_4135438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135438).length < 2 ^ (prefixWord ++ tailWord_4135438).sum := by decide
  have hdescent : baseEnd_4135438 < baseStart_4135438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135481 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_4135481 : Nat := 118140960795 + 4135481 * 2 ^ 59
def prefixEnd_4135481 : Nat := 4983230072969 + 3 ^ 40 * 4135481 * 2
def baseEnd_4135481 : Nat := 707829830178746548422925

theorem tailTrace_4135481 : CollatzResearch.WordTrace tailWord_4135481 prefixEnd_4135481 707829830178746548422925 := by
  unfold tailWord_4135481
  simp only [CollatzResearch.WordTrace]
  refine ⟨150833383530866095769774297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100555589020577397179849531 150833383530866095769774297)
  ·
    refine ⟨113125037648149571827330723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150833383530866095769774297 113125037648149571827330723)
    ·
      refine ⟨169687556472224357740996085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113125037648149571827330723 169687556472224357740996085)
      ·
        refine ⟨15908208419271033538218383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169687556472224357740996085 15908208419271033538218383)
        ·
          refine ⟨23862312628906550307327575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908208419271033538218383 23862312628906550307327575)
          ·
            refine ⟨35793468943359825460991363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23862312628906550307327575 35793468943359825460991363)
            ·
              refine ⟨53690203415039738191487045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35793468943359825460991363 53690203415039738191487045)
              ·
                refine ⟨10066913140319950910903821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53690203415039738191487045 10066913140319950910903821)
                ·
                  refine ⟨3775092427619981591588933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10066913140319950910903821 3775092427619981591588933)
                  ·
                    refine ⟨707829830178746548422925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775092427619981591588933 707829830178746548422925)
                    ·
                      rfl

theorem cell23_4135481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_4135481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135481 prefixEnd_4135481 := by exact prefixLift 4135481
  have htrace : WordTrace (prefixWord ++ tailWord_4135481) baseStart_4135481 baseEnd_4135481 := by
    simpa [prefixWord, tailWord_4135481, baseEnd_4135481] using wordTrace_append hprefix tailTrace_4135481
  have hstable : (prefixWord ++ tailWord_4135481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135481).length < 2 ^ (prefixWord ++ tailWord_4135481).sum := by decide
  have hdescent : baseEnd_4135481 < baseStart_4135481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135508 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_4135508 : Nat := 118140960795 + 4135508 * 2 ^ 59
def prefixEnd_4135508 : Nat := 4983230072969 + 3 ^ 40 * 4135508 * 2
def baseEnd_4135508 : Nat := 2123503354513911039631151

theorem tailTrace_4135508 : CollatzResearch.WordTrace tailWord_4135508 prefixEnd_4135508 2123503354513911039631151 := by
  unfold tailWord_4135508
  simp only [CollatzResearch.WordTrace]
  refine ⟨75417184150884139690503589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100556245534512186254004785 75417184150884139690503589)
  ·
    refine ⟨14140722028290776191969423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75417184150884139690503589 14140722028290776191969423)
    ·
      refine ⟨21211083042436164287954135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14140722028290776191969423 21211083042436164287954135)
      ·
        refine ⟨31816624563654246431931203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21211083042436164287954135 31816624563654246431931203)
        ·
          refine ⟨47724936845481369647896805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31816624563654246431931203 47724936845481369647896805)
          ·
            refine ⟨8948425658527756808980651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47724936845481369647896805 8948425658527756808980651)
            ·
              refine ⟨13422638487791635213470977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948425658527756808980651 13422638487791635213470977)
              ·
                refine ⟨10066978865843726410103233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13422638487791635213470977 10066978865843726410103233)
                ·
                  refine ⟨7550234149382794807577425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066978865843726410103233 7550234149382794807577425)
                  ·
                    refine ⟨5662675612037096105683069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7550234149382794807577425 5662675612037096105683069)
                    ·
                      refine ⟨2123503354513911039631151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662675612037096105683069 2123503354513911039631151)
                      ·
                        rfl

theorem cell23_4135508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_4135508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135508 prefixEnd_4135508 := by exact prefixLift 4135508
  have htrace : WordTrace (prefixWord ++ tailWord_4135508) baseStart_4135508 baseEnd_4135508 := by
    simpa [prefixWord, tailWord_4135508, baseEnd_4135508] using wordTrace_append hprefix tailTrace_4135508
  have hstable : (prefixWord ++ tailWord_4135508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135508).length < 2 ^ (prefixWord ++ tailWord_4135508).sum := by decide
  have hdescent : baseEnd_4135508 < baseStart_4135508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135528 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 6]
def baseStart_4135528 : Nat := 118140960795 + 4135528 * 2 ^ 59
def prefixEnd_4135528 : Nat := 4983230072969 + 3 ^ 40 * 4135528 * 2
def baseEnd_4135528 : Nat := 235945958236333440153451

theorem tailTrace_4135528 : CollatzResearch.WordTrace tailWord_4135528 prefixEnd_4135528 235945958236333440153451 := by
  unfold tailWord_4135528
  simp only [CollatzResearch.WordTrace]
  refine ⟨75417548880847911398367619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100556731841130548531156825 75417548880847911398367619)
  ·
    refine ⟨113126323321271867097551429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75417548880847911398367619 113126323321271867097551429)
    ·
      refine ⟨21211185622738475080790893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113126323321271867097551429 21211185622738475080790893)
      ·
        refine ⟨7954194608526928155296585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21211185622738475080790893 7954194608526928155296585)
        ·
          refine ⟨5965645956395196116472439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954194608526928155296585 5965645956395196116472439)
          ·
            refine ⟨8948468934592794174708659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965645956395196116472439 8948468934592794174708659)
            ·
              refine ⟨13422703401889191262062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948468934592794174708659 13422703401889191262062989)
              ·
                refine ⟨5033513775708446723273621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13422703401889191262062989 5033513775708446723273621)
                ·
                  refine ⟨235945958236333440153451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5033513775708446723273621 235945958236333440153451)
                  ·
                    rfl

theorem cell23_4135528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_4135528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135528 prefixEnd_4135528 := by exact prefixLift 4135528
  have htrace : WordTrace (prefixWord ++ tailWord_4135528) baseStart_4135528 baseEnd_4135528 := by
    simpa [prefixWord, tailWord_4135528, baseEnd_4135528] using wordTrace_append hprefix tailTrace_4135528
  have hstable : (prefixWord ++ tailWord_4135528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135528).length < 2 ^ (prefixWord ++ tailWord_4135528).sum := by decide
  have hdescent : baseEnd_4135528 < baseStart_4135528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135531 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 5, 2]
def baseStart_4135531 : Nat := 118140960795 + 4135531 * 2 ^ 59
def prefixEnd_4135531 : Nat := 4983230072969 + 3 ^ 40 * 4135531 * 2
def baseEnd_4135531 : Nat := 2123515164568964449643545

theorem tailTrace_4135531 : CollatzResearch.WordTrace tailWord_4135531 prefixEnd_4135531 2123515164568964449643545 := by
  unfold tailWord_4135531
  simp only [CollatzResearch.WordTrace]
  refine ⟨150835207180684954309094447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100556804787123302872729631 150835207180684954309094447)
  ·
    refine ⟨226252810771027431463641671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150835207180684954309094447 226252810771027431463641671)
    ·
      refine ⟨339379216156541147195462507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226252810771027431463641671 339379216156541147195462507)
      ·
        refine ⟨509068824234811720793193761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339379216156541147195462507 509068824234811720793193761)
        ·
          refine ⟨381801618176108790594895321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509068824234811720793193761 381801618176108790594895321)
          ·
            refine ⟨286351213632081592946171491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381801618176108790594895321 286351213632081592946171491)
            ·
              refine ⟨429526820448122389419257237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286351213632081592946171491 429526820448122389419257237)
              ·
                refine ⟨20134069708505737004027683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 429526820448122389419257237 20134069708505737004027683)
                ·
                  refine ⟨30201104562758605506041525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20134069708505737004027683 30201104562758605506041525)
                  ·
                    refine ⟨2831353552758619266191393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30201104562758605506041525 2831353552758619266191393)
                    ·
                      refine ⟨2123515164568964449643545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831353552758619266191393 2123515164568964449643545)
                      ·
                        rfl

theorem cell23_4135531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5, 2].length) (baseStart_4135531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135531 prefixEnd_4135531 := by exact prefixLift 4135531
  have htrace : WordTrace (prefixWord ++ tailWord_4135531) baseStart_4135531 baseEnd_4135531 := by
    simpa [prefixWord, tailWord_4135531, baseEnd_4135531] using wordTrace_append hprefix tailTrace_4135531
  have hstable : (prefixWord ++ tailWord_4135531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135531).length < 2 ^ (prefixWord ++ tailWord_4135531).sum := by decide
  have hdescent : baseEnd_4135531 < baseStart_4135531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135544 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_4135544 : Nat := 118140960795 + 4135544 * 2 ^ 59
def prefixEnd_4135544 : Nat := 4983230072969 + 3 ^ 40 * 4135544 * 2
def baseEnd_4135544 : Nat := 2123521839817472898780985

theorem tailTrace_4135544 : CollatzResearch.WordTrace tailWord_4135544 prefixEnd_4135544 2123521839817472898780985 := by
  unfold tailWord_4135544
  simp only [CollatzResearch.WordTrace]
  refine ⟨75417840664818928764658843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100557120886425238352878457 75417840664818928764658843)
  ·
    refine ⟨113126760997228393146988265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75417840664818928764658843 113126760997228393146988265)
    ·
      refine ⟨84845070747921294860241199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113126760997228393146988265 84845070747921294860241199)
      ·
        refine ⟨127267606121881942290361799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84845070747921294860241199 127267606121881942290361799)
        ·
          refine ⟨190901409182822913435542699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127267606121881942290361799 190901409182822913435542699)
          ·
            refine ⟨286352113774234370153314049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190901409182822913435542699 286352113774234370153314049)
            ·
              refine ⟨214764085330675777614985537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286352113774234370153314049 214764085330675777614985537)
              ·
                refine ⟨161073063998006833211239153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214764085330675777614985537 161073063998006833211239153)
                ·
                  refine ⟨120804797998505124908429365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161073063998006833211239153 120804797998505124908429365)
                  ·
                    refine ⟨11325449812359855460165253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120804797998505124908429365 11325449812359855460165253)
                    ·
                      refine ⟨2123521839817472898780985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11325449812359855460165253 2123521839817472898780985)
                      ·
                        rfl

theorem cell23_4135544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_4135544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135544 prefixEnd_4135544 := by exact prefixLift 4135544
  have htrace : WordTrace (prefixWord ++ tailWord_4135544) baseStart_4135544 baseEnd_4135544 := by
    simpa [prefixWord, tailWord_4135544, baseEnd_4135544] using wordTrace_append hprefix tailTrace_4135544
  have hstable : (prefixWord ++ tailWord_4135544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135544).length < 2 ^ (prefixWord ++ tailWord_4135544).sum := by decide
  have hdescent : baseEnd_4135544 < baseStart_4135544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135548 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_4135548 : Nat := 118140960795 + 4135548 * 2 ^ 59
def prefixEnd_4135548 : Nat := 4983230072969 + 3 ^ 40 * 4135548 * 2
def baseEnd_4135548 : Nat := 2123523893740090883130967

theorem tailTrace_4135548 : CollatzResearch.WordTrace tailWord_4135548 prefixEnd_4135548 2123523893740090883130967 := by
  unfold tailWord_4135548
  simp only [CollatzResearch.WordTrace]
  refine ⟨75417913610811683106231649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100557218147748910808308865 75417913610811683106231649)
  ·
    refine ⟨56563435208108762329673737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75417913610811683106231649 56563435208108762329673737)
    ·
      refine ⟨42422576406081571747255303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56563435208108762329673737 42422576406081571747255303)
      ·
        refine ⟨63633864609122357620882955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42422576406081571747255303 63633864609122357620882955)
        ·
          refine ⟨95450796913683536431324433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63633864609122357620882955 95450796913683536431324433)
          ·
            refine ⟨71588097685262652323493325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95450796913683536431324433 71588097685262652323493325)
            ·
              refine ⟨26845536631973494621309997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71588097685262652323493325 26845536631973494621309997)
              ·
                refine ⟨10067076236990060482991249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26845536631973494621309997 10067076236990060482991249)
                ·
                  refine ⟨7550307177742545362243437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10067076236990060482991249 7550307177742545362243437)
                  ·
                    refine ⟨2831365191653454510841289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7550307177742545362243437 2831365191653454510841289)
                    ·
                      refine ⟨2123523893740090883130967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831365191653454510841289 2123523893740090883130967)
                      ·
                        rfl

theorem cell23_4135548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_4135548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135548 prefixEnd_4135548 := by exact prefixLift 4135548
  have htrace : WordTrace (prefixWord ++ tailWord_4135548) baseStart_4135548 baseEnd_4135548 := by
    simpa [prefixWord, tailWord_4135548, baseEnd_4135548] using wordTrace_append hprefix tailTrace_4135548
  have hstable : (prefixWord ++ tailWord_4135548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135548).length < 2 ^ (prefixWord ++ tailWord_4135548).sum := by decide
  have hdescent : baseEnd_4135548 < baseStart_4135548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135581 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4135581 : Nat := 118140960795 + 4135581 * 2 ^ 59
def prefixEnd_4135581 : Nat := 4983230072969 + 3 ^ 40 * 4135581 * 2
def baseEnd_4135581 : Nat := 2123540838601689254018315

theorem tailTrace_4135581 : CollatzResearch.WordTrace tailWord_4135581 prefixEnd_4135581 2123540838601689254018315 := by
  unfold tailWord_4135581
  simp only [CollatzResearch.WordTrace]
  refine ⟨150837030830503812848414597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100558020553669208565609731 150837030830503812848414597)
  ·
    refine ⟨28281943280719464909077737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150837030830503812848414597 28281943280719464909077737)
    ·
      refine ⟨21211457460539598681808303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28281943280719464909077737 21211457460539598681808303)
      ·
        refine ⟨31817186190809398022712455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21211457460539598681808303 31817186190809398022712455)
        ·
          refine ⟨47725779286214097034068683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31817186190809398022712455 47725779286214097034068683)
          ·
            refine ⟨71588668929321145551103025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47725779286214097034068683 71588668929321145551103025)
            ·
              refine ⟨53691501696990859163327269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71588668929321145551103025 53691501696990859163327269)
              ·
                refine ⟨10067156568185786093123863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53691501696990859163327269 10067156568185786093123863)
                ·
                  refine ⟨15100734852278679139685795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067156568185786093123863 15100734852278679139685795)
                  ·
                    refine ⟨22651102278418018709528693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15100734852278679139685795 22651102278418018709528693)
                    ·
                      refine ⟨2123540838601689254018315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22651102278418018709528693 2123540838601689254018315)
                      ·
                        rfl

theorem cell23_4135581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4135581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135581 prefixEnd_4135581 := by exact prefixLift 4135581
  have htrace : WordTrace (prefixWord ++ tailWord_4135581) baseStart_4135581 baseEnd_4135581 := by
    simpa [prefixWord, tailWord_4135581, baseEnd_4135581] using wordTrace_append hprefix tailTrace_4135581
  have hstable : (prefixWord ++ tailWord_4135581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135581).length < 2 ^ (prefixWord ++ tailWord_4135581).sum := by decide
  have hdescent : baseEnd_4135581 < baseStart_4135581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135588 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_4135588 : Nat := 118140960795 + 4135588 * 2 ^ 59
def prefixEnd_4135588 : Nat := 4983230072969 + 3 ^ 40 * 4135588 * 2
def baseEnd_4135588 : Nat := 707848144322090242210261

theorem tailTrace_4135588 : CollatzResearch.WordTrace tailWord_4135588 prefixEnd_4135588 707848144322090242210261 := by
  unfold tailWord_4135588
  simp only [CollatzResearch.WordTrace]
  refine ⟨75418643070739226521959709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100558190760985635362612945 75418643070739226521959709)
  ·
    refine ⟨28281991151527209945734891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75418643070739226521959709 28281991151527209945734891)
    ·
      refine ⟨42422986727290814918602337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28281991151527209945734891 42422986727290814918602337)
      ·
        refine ⟨31817240045468111188951753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42422986727290814918602337 31817240045468111188951753)
        ·
          refine ⟨23862930034101083391713815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31817240045468111188951753 23862930034101083391713815)
          ·
            refine ⟨35794395051151625087570723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23862930034101083391713815 35794395051151625087570723)
            ·
              refine ⟨53691592576727437631356085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35794395051151625087570723 53691592576727437631356085)
              ·
                refine ⟨5033586804068197277939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53691592576727437631356085 5033586804068197277939633)
                ·
                  refine ⟨3775190103051147958454725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033586804068197277939633 3775190103051147958454725)
                  ·
                    refine ⟨707848144322090242210261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775190103051147958454725 707848144322090242210261)
                    ·
                      rfl

theorem cell23_4135588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_4135588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135588 prefixEnd_4135588 := by exact prefixLift 4135588
  have htrace : WordTrace (prefixWord ++ tailWord_4135588) baseStart_4135588 baseEnd_4135588 := by
    simpa [prefixWord, tailWord_4135588, baseEnd_4135588] using wordTrace_append hprefix tailTrace_4135588
  have hstable : (prefixWord ++ tailWord_4135588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135588).length < 2 ^ (prefixWord ++ tailWord_4135588).sum := by decide
  have hdescent : baseEnd_4135588 < baseStart_4135588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135606 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4135606 : Nat := 118140960795 + 4135606 * 2 ^ 59
def prefixEnd_4135606 : Nat := 4983230072969 + 3 ^ 40 * 4135606 * 2
def baseEnd_4135606 : Nat := 2123553675618051656205701

theorem tailTrace_4135606 : CollatzResearch.WordTrace tailWord_4135606 prefixEnd_4135606 2123553675618051656205701 := by
  unfold tailWord_4135606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9427371415963327632379667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100558628436942161412049781 9427371415963327632379667)
  ·
    refine ⟨14141057123944991448569501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9427371415963327632379667 14141057123944991448569501)
    ·
      refine ⟨5302896421479371793213563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14141057123944991448569501 5302896421479371793213563)
      ·
        refine ⟨7954344632219057689820345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302896421479371793213563 7954344632219057689820345)
        ·
          refine ⟨5965758474164293267365259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954344632219057689820345 5965758474164293267365259)
          ·
            refine ⟨8948637711246439901047889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965758474164293267365259 8948637711246439901047889)
            ·
              refine ⟨6711478283434829925785917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948637711246439901047889 6711478283434829925785917)
              ·
                refine ⟨2516804356288061222169719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6711478283434829925785917 2516804356288061222169719)
                ·
                  refine ⟨3775206534432091833254579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516804356288061222169719 3775206534432091833254579)
                  ·
                    refine ⟨5662809801648137749881869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3775206534432091833254579 5662809801648137749881869)
                    ·
                      refine ⟨2123553675618051656205701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662809801648137749881869 2123553675618051656205701)
                      ·
                        rfl

theorem cell23_4135606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4135606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135606 prefixEnd_4135606 := by exact prefixLift 4135606
  have htrace : WordTrace (prefixWord ++ tailWord_4135606) baseStart_4135606 baseEnd_4135606 := by
    simpa [prefixWord, tailWord_4135606, baseEnd_4135606] using wordTrace_append hprefix tailTrace_4135606
  have hstable : (prefixWord ++ tailWord_4135606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135606).length < 2 ^ (prefixWord ++ tailWord_4135606).sum := by decide
  have hdescent : baseEnd_4135606 < baseStart_4135606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135615 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 1, 2, 3]
def baseStart_4135615 : Nat := 118140960795 + 4135615 * 2 ^ 59
def prefixEnd_4135615 : Nat := 4983230072969 + 3 ^ 40 * 4135615 * 2
def baseEnd_4135615 : Nat := 2123558296943942120993159

theorem tailTrace_4135615 : CollatzResearch.WordTrace tailWord_4135615 prefixEnd_4135615 2123558296943942120993159 := by
  unfold tailWord_4135615
  simp only [CollatzResearch.WordTrace]
  refine ⟨150838270912380636655152299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100558847274920424436768199 150838270912380636655152299)
  ·
    refine ⟨226257406368570954982728449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150838270912380636655152299 226257406368570954982728449)
    ·
      refine ⟨169693054776428216237046337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226257406368570954982728449 169693054776428216237046337)
      ·
        refine ⟨127269791082321162177784753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169693054776428216237046337 127269791082321162177784753)
        ·
          refine ⟨95452343311740871633338565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127269791082321162177784753 95452343311740871633338565)
          ·
            refine ⟨17897314370951413431250981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95452343311740871633338565 17897314370951413431250981)
            ·
              refine ⟨3355746444553390018359559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17897314370951413431250981 3355746444553390018359559)
              ·
                refine ⟨5033619666830085027539339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355746444553390018359559 5033619666830085027539339)
                ·
                  refine ⟨7550429500245127541309009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033619666830085027539339 7550429500245127541309009)
                  ·
                    refine ⟨5662822125183845655981757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7550429500245127541309009 5662822125183845655981757)
                    ·
                      refine ⟨2123558296943942120993159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662822125183845655981757 2123558296943942120993159)
                      ·
                        rfl

theorem cell23_4135615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_4135615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135615 prefixEnd_4135615 := by exact prefixLift 4135615
  have htrace : WordTrace (prefixWord ++ tailWord_4135615) baseStart_4135615 baseEnd_4135615 := by
    simpa [prefixWord, tailWord_4135615, baseEnd_4135615] using wordTrace_append hprefix tailTrace_4135615
  have hstable : (prefixWord ++ tailWord_4135615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135615).length < 2 ^ (prefixWord ++ tailWord_4135615).sum := by decide
  have hdescent : baseEnd_4135615 < baseStart_4135615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135671 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_4135671 : Nat := 118140960795 + 4135671 * 2 ^ 59
def prefixEnd_4135671 : Nat := 4983230072969 + 3 ^ 40 * 4135671 * 2
def baseEnd_4135671 : Nat := 2123587051860593901892901

theorem tailTrace_4135671 : CollatzResearch.WordTrace tailWord_4135671 prefixEnd_4135671 2123587051860593901892901 := by
  unfold tailWord_4135671
  simp only [CollatzResearch.WordTrace]
  refine ⟨150840313400177758219190867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100560208933451838812793911 150840313400177758219190867)
  ·
    refine ⟨226260470100266637328786301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150840313400177758219190867 226260470100266637328786301)
    ·
      refine ⟨84847676287599988998294863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226260470100266637328786301 84847676287599988998294863)
      ·
        refine ⟨127271514431399983497442295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84847676287599988998294863 127271514431399983497442295)
        ·
          refine ⟨190907271647099975246163443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127271514431399983497442295 190907271647099975246163443)
          ·
            refine ⟨286360907470649962869245165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190907271647099975246163443 286360907470649962869245165)
            ·
              refine ⟨107385340301493736075966937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286360907470649962869245165 107385340301493736075966937)
              ·
                refine ⟨80539005226120302056975203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107385340301493736075966937 80539005226120302056975203)
                ·
                  refine ⟨120808507839180453085462805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80539005226120302056975203 120808507839180453085462805)
                  ·
                    refine ⟨5662898804961583738381069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120808507839180453085462805 5662898804961583738381069)
                    ·
                      refine ⟨2123587051860593901892901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5662898804961583738381069 2123587051860593901892901)
                      ·
                        rfl

theorem cell23_4135671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_4135671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135671 prefixEnd_4135671 := by exact prefixLift 4135671
  have htrace : WordTrace (prefixWord ++ tailWord_4135671) baseStart_4135671 baseEnd_4135671 := by
    simpa [prefixWord, tailWord_4135671, baseEnd_4135671] using wordTrace_append hprefix tailTrace_4135671
  have hstable : (prefixWord ++ tailWord_4135671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135671).length < 2 ^ (prefixWord ++ tailWord_4135671).sum := by decide
  have hdescent : baseEnd_4135671 < baseStart_4135671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135721 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_4135721 : Nat := 118140960795 + 4135721 * 2 ^ 59
def prefixEnd_4135721 : Nat := 4983230072969 + 3 ^ 40 * 4135721 * 2
def baseEnd_4135721 : Nat := 707870908631106235422557

theorem tailTrace_4135721 : CollatzResearch.WordTrace tailWord_4135721 prefixEnd_4135721 707870908631106235422557 := by
  unfold tailWord_4135721
  simp only [CollatzResearch.WordTrace]
  refine ⟨150842137049996616758511017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100561424699997744505674011 150842137049996616758511017)
  ·
    refine ⟨113131602787497462568883263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150842137049996616758511017 113131602787497462568883263)
    ·
      refine ⟨169697404181246193853324895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113131602787497462568883263 169697404181246193853324895)
      ·
        refine ⟨254546106271869290779987343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169697404181246193853324895 254546106271869290779987343)
        ·
          refine ⟨381819159407803936169981015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254546106271869290779987343 381819159407803936169981015)
          ·
            refine ⟨572728739111705904254971523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381819159407803936169981015 572728739111705904254971523)
            ·
              refine ⟨859093108667558856382457285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572728739111705904254971523 859093108667558856382457285)
              ·
                refine ⟨161079957875167285571710741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 859093108667558856382457285 161079957875167285571710741)
                ·
                  refine ⟨7550623025398466511173941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161079957875167285571710741 7550623025398466511173941)
                  ·
                    refine ⟨707870908631106235422557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7550623025398466511173941 707870908631106235422557)
                    ·
                      rfl

theorem cell23_4135721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_4135721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135721 prefixEnd_4135721 := by exact prefixLift 4135721
  have htrace : WordTrace (prefixWord ++ tailWord_4135721) baseStart_4135721 baseEnd_4135721 := by
    simpa [prefixWord, tailWord_4135721, baseEnd_4135721] using wordTrace_append hprefix tailTrace_4135721
  have hstable : (prefixWord ++ tailWord_4135721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135721).length < 2 ^ (prefixWord ++ tailWord_4135721).sum := by decide
  have hdescent : baseEnd_4135721 < baseStart_4135721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135728 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2]
def baseStart_4135728 : Nat := 118140960795 + 4135728 * 2 ^ 59
def prefixEnd_4135728 : Nat := 4983230072969 + 3 ^ 40 * 4135728 * 2
def baseEnd_4135728 : Nat := 2123616320257900178880139

theorem tailTrace_4135728 : CollatzResearch.WordTrace tailWord_4135728 prefixEnd_4135728 2123616320257900178880139 := by
  unfold tailWord_4135728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75421196180485628477007919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100561594907314171302677225 75421196180485628477007919)
  ·
    refine ⟨113131794270728442715511879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75421196180485628477007919 113131794270728442715511879)
    ·
      refine ⟨169697691406092664073267819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113131794270728442715511879 169697691406092664073267819)
      ·
        refine ⟨254546537109138996109901729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169697691406092664073267819 254546537109138996109901729)
        ·
          refine ⟨190909902831854247082426297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254546537109138996109901729 190909902831854247082426297)
          ·
            refine ⟨143182427123890685311819723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190909902831854247082426297 143182427123890685311819723)
            ·
              refine ⟨214773640685836027967729585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143182427123890685311819723 214773640685836027967729585)
              ·
                refine ⟨161080230514377020975797189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214773640685836027967729585 161080230514377020975797189)
                ·
                  refine ⟨30202543221445691432961973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161080230514377020975797189 30202543221445691432961973)
                  ·
                    refine ⟨2831488427010533571840185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30202543221445691432961973 2831488427010533571840185)
                    ·
                      refine ⟨2123616320257900178880139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831488427010533571840185 2123616320257900178880139)
                      ·
                        rfl

theorem cell23_4135728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2].length) (baseStart_4135728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135728 prefixEnd_4135728 := by exact prefixLift 4135728
  have htrace : WordTrace (prefixWord ++ tailWord_4135728) baseStart_4135728 baseEnd_4135728 := by
    simpa [prefixWord, tailWord_4135728, baseEnd_4135728] using wordTrace_append hprefix tailTrace_4135728
  have hstable : (prefixWord ++ tailWord_4135728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135728).length < 2 ^ (prefixWord ++ tailWord_4135728).sum := by decide
  have hdescent : baseEnd_4135728 < baseStart_4135728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135742 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_4135742 : Nat := 118140960795 + 4135742 * 2 ^ 59
def prefixEnd_4135742 : Nat := 4983230072969 + 3 ^ 40 * 4135742 * 2
def baseEnd_4135742 : Nat := 235958167665229236011675

theorem tailTrace_4135742 : CollatzResearch.WordTrace tailWord_4135742 prefixEnd_4135742 235958167665229236011675 := by
  unfold tailWord_4135742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855362872865067168128185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100561935321947024896683653 18855362872865067168128185)
  ·
    refine ⟨14141522154648800376096139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18855362872865067168128185 14141522154648800376096139)
    ·
      refine ⟨21212283231973200564144209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14141522154648800376096139 21212283231973200564144209)
      ·
        refine ⟨15909212423979900423108157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21212283231973200564144209 15909212423979900423108157)
        ·
          refine ⟨5965954658992462658665559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15909212423979900423108157 5965954658992462658665559)
          ·
            refine ⟨8948931988488693987998339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965954658992462658665559 8948931988488693987998339)
            ·
              refine ⟨13423397982733040981997509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948931988488693987998339 13423397982733040981997509)
              ·
                refine ⟨2516887121762445184124533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13423397982733040981997509 2516887121762445184124533)
                ·
                  refine ⟨235958167665229236011675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2516887121762445184124533 235958167665229236011675)
                  ·
                    rfl

theorem cell23_4135742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_4135742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135742 prefixEnd_4135742 := by exact prefixLift 4135742
  have htrace : WordTrace (prefixWord ++ tailWord_4135742) baseStart_4135742 baseEnd_4135742 := by
    simpa [prefixWord, tailWord_4135742, baseEnd_4135742] using wordTrace_append hprefix tailTrace_4135742
  have hstable : (prefixWord ++ tailWord_4135742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135742).length < 2 ^ (prefixWord ++ tailWord_4135742).sum := by decide
  have hdescent : baseEnd_4135742 < baseStart_4135742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135751 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 8]
def baseStart_4135751 : Nat := 118140960795 + 4135751 * 2 ^ 59
def prefixEnd_4135751 : Nat := 4983230072969 + 3 ^ 40 * 4135751 * 2
def baseEnd_4135751 : Nat := 707876043437651196297511

theorem tailTrace_4135751 : CollatzResearch.WordTrace tailWord_4135751 prefixEnd_4135751 707876043437651196297511 := by
  unfold tailWord_4135751
  simp only [CollatzResearch.WordTrace]
  refine ⟨150843231239887931882103107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100562154159925287921402071 150843231239887931882103107)
  ·
    refine ⟨226264846859831897823154661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150843231239887931882103107 226264846859831897823154661)
    ·
      refine ⟨42424658786218480841841499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226264846859831897823154661 42424658786218480841841499)
      ·
        refine ⟨63636988179327721262762249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42424658786218480841841499 63636988179327721262762249)
        ·
          refine ⟨47727741134495790947071687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63636988179327721262762249 47727741134495790947071687)
          ·
            refine ⟨71591611701743686420607531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47727741134495790947071687 71591611701743686420607531)
            ·
              refine ⟨107387417552615529630911297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71591611701743686420607531 107387417552615529630911297)
              ·
                refine ⟨80540563164461647223183473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107387417552615529630911297 80540563164461647223183473)
                ·
                  refine ⟨60405422373346235417387605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80540563164461647223183473 60405422373346235417387605)
                  ·
                    refine ⟨707876043437651196297511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60405422373346235417387605 707876043437651196297511)
                    ·
                      rfl

theorem cell23_4135751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_4135751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135751 prefixEnd_4135751 := by exact prefixLift 4135751
  have htrace : WordTrace (prefixWord ++ tailWord_4135751) baseStart_4135751 baseEnd_4135751 := by
    simpa [prefixWord, tailWord_4135751, baseEnd_4135751] using wordTrace_append hprefix tailTrace_4135751
  have hstable : (prefixWord ++ tailWord_4135751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135751).length < 2 ^ (prefixWord ++ tailWord_4135751).sum := by decide
  have hdescent : baseEnd_4135751 < baseStart_4135751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135758 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4135758 : Nat := 118140960795 + 4135758 * 2 ^ 59
def prefixEnd_4135758 : Nat := 4983230072969 + 3 ^ 40 * 4135758 * 2
def baseEnd_4135758 : Nat := 2123631724677535061505001

theorem tailTrace_4135758 : CollatzResearch.WordTrace tailWord_4135758 prefixEnd_4135758 2123631724677535061505001 := by
  unfold tailWord_4135758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855435818857821509700991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100562324367241714718405285 18855435818857821509700991)
  ·
    refine ⟨28283153728286732264551487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18855435818857821509700991 28283153728286732264551487)
    ·
      refine ⟨42424730592430098396827231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28283153728286732264551487 42424730592430098396827231)
      ·
        refine ⟨63637095888645147595240847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42424730592430098396827231 63637095888645147595240847)
        ·
          refine ⟨95455643832967721392861271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63637095888645147595240847 95455643832967721392861271)
          ·
            refine ⟨143183465749451582089291907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95455643832967721392861271 143183465749451582089291907)
            ·
              refine ⟨214775198624177373133937861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143183465749451582089291907 214775198624177373133937861)
              ·
                refine ⟨40270349742033257462613349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214775198624177373133937861 40270349742033257462613349)
                ·
                  refine ⟨7550690576631235774240003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40270349742033257462613349 7550690576631235774240003)
                  ·
                    refine ⟨11326035864946853661360005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7550690576631235774240003 11326035864946853661360005)
                    ·
                      refine ⟨2123631724677535061505001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11326035864946853661360005 2123631724677535061505001)
                      ·
                        rfl

theorem cell23_4135758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4135758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135758 prefixEnd_4135758 := by exact prefixLift 4135758
  have htrace : WordTrace (prefixWord ++ tailWord_4135758) baseStart_4135758 baseEnd_4135758 := by
    simpa [prefixWord, tailWord_4135758, baseEnd_4135758] using wordTrace_append hprefix tailTrace_4135758
  have hstable : (prefixWord ++ tailWord_4135758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135758).length < 2 ^ (prefixWord ++ tailWord_4135758).sum := by decide
  have hdescent : baseEnd_4135758 < baseStart_4135758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135772 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4135772 : Nat := 118140960795 + 4135772 * 2 ^ 59
def prefixEnd_4135772 : Nat := 4983230072969 + 3 ^ 40 * 4135772 * 2
def baseEnd_4135772 : Nat := 707879637802232668909979

theorem tailTrace_4135772 : CollatzResearch.WordTrace tailWord_4135772 prefixEnd_4135772 707879637802232668909979 := by
  unfold tailWord_4135772
  simp only [CollatzResearch.WordTrace]
  refine ⟨75421998586405926234308785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100562664781874568312411713 75421998586405926234308785)
  ·
    refine ⟨56566498939804444675731589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75421998586405926234308785 56566498939804444675731589)
    ·
      refine ⟨10606218551213333376699673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56566498939804444675731589 10606218551213333376699673)
      ·
        refine ⟨7954663913410000032524755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10606218551213333376699673 7954663913410000032524755)
        ·
          refine ⟨11931995870115000048787133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954663913410000032524755 11931995870115000048787133)
          ·
            refine ⟨4474498451293125018295175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11931995870115000048787133 4474498451293125018295175)
            ·
              refine ⟨6711747676939687527442763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474498451293125018295175 6711747676939687527442763)
              ·
                refine ⟨10067621515409531291164145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711747676939687527442763 10067621515409531291164145)
                ·
                  refine ⟨7550716136557148468373109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10067621515409531291164145 7550716136557148468373109)
                  ·
                    refine ⟨707879637802232668909979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7550716136557148468373109 707879637802232668909979)
                    ·
                      rfl

theorem cell23_4135772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4135772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135772 prefixEnd_4135772 := by exact prefixLift 4135772
  have htrace : WordTrace (prefixWord ++ tailWord_4135772) baseStart_4135772 baseEnd_4135772 := by
    simpa [prefixWord, tailWord_4135772, baseEnd_4135772] using wordTrace_append hprefix tailTrace_4135772
  have hstable : (prefixWord ++ tailWord_4135772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135772).length < 2 ^ (prefixWord ++ tailWord_4135772).sum := by decide
  have hdescent : baseEnd_4135772 < baseStart_4135772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135836 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_4135836 : Nat := 118140960795 + 4135836 * 2 ^ 59
def prefixEnd_4135836 : Nat := 4983230072969 + 3 ^ 40 * 4135836 * 2
def baseEnd_4135836 : Nat := 707890592056195252109881

theorem tailTrace_4135836 : CollatzResearch.WordTrace tailWord_4135836 prefixEnd_4135836 707890592056195252109881 := by
  unfold tailWord_4135836
  simp only [CollatzResearch.WordTrace]
  refine ⟨75423165722289995699473681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100564220963053327599298241 75423165722289995699473681)
  ·
    refine ⟨56567374291717496774605261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75423165722289995699473681 56567374291717496774605261)
    ·
      refine ⟨21212765359394061290476973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56567374291717496774605261 21212765359394061290476973)
      ·
        refine ⟨7954787009772772983928865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21212765359394061290476973 7954787009772772983928865)
        ·
          refine ⟨5966090257329579737946649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954787009772772983928865 5966090257329579737946649)
          ·
            refine ⟨4474567692997184803459987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5966090257329579737946649 4474567692997184803459987)
            ·
              refine ⟨6711851539495777205189981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474567692997184803459987 6711851539495777205189981)
              ·
                refine ⟨2516944327310916451946243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6711851539495777205189981 2516944327310916451946243)
                ·
                  refine ⟨3775416490966374677919365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516944327310916451946243 3775416490966374677919365)
                  ·
                    refine ⟨707890592056195252109881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775416490966374677919365 707890592056195252109881)
                    ·
                      rfl

theorem cell23_4135836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_4135836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135836 prefixEnd_4135836 := by exact prefixLift 4135836
  have htrace : WordTrace (prefixWord ++ tailWord_4135836) baseStart_4135836 baseEnd_4135836 := by
    simpa [prefixWord, tailWord_4135836, baseEnd_4135836] using wordTrace_append hprefix tailTrace_4135836
  have hstable : (prefixWord ++ tailWord_4135836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135836).length < 2 ^ (prefixWord ++ tailWord_4135836).sum := by decide
  have hdescent : baseEnd_4135836 < baseStart_4135836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135853 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4135853 : Nat := 118140960795 + 4135853 * 2 ^ 59
def prefixEnd_4135853 : Nat := 4983230072969 + 3 ^ 40 * 4135853 * 2
def baseEnd_4135853 : Nat := 707893501779904063272355

theorem tailTrace_4135853 : CollatzResearch.WordTrace tailWord_4135853 prefixEnd_4135853 707893501779904063272355 := by
  unfold tailWord_4135853
  simp only [CollatzResearch.WordTrace]
  refine ⟨150846951485518403302316213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100564634323678935534877475 150846951485518403302316213)
  ·
    refine ⟨14141901701767350309592145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150846951485518403302316213 14141901701767350309592145)
    ·
      refine ⟨10606426276325512732194109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14141901701767350309592145 10606426276325512732194109)
      ·
        refine ⟨3977409853622067274572791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10606426276325512732194109 3977409853622067274572791)
        ·
          refine ⟨5966114780433100911859187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977409853622067274572791 5966114780433100911859187)
          ·
            refine ⟨8949172170649651367788781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5966114780433100911859187 8949172170649651367788781)
            ·
              refine ⟨3355939563993619262920793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8949172170649651367788781 3355939563993619262920793)
              ·
                refine ⟨2516954672995214447190595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355939563993619262920793 2516954672995214447190595)
                ·
                  refine ⟨3775432009492821670785893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516954672995214447190595 3775432009492821670785893)
                  ·
                    refine ⟨707893501779904063272355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775432009492821670785893 707893501779904063272355)
                    ·
                      rfl

theorem cell23_4135853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4135853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135853 prefixEnd_4135853 := by exact prefixLift 4135853
  have htrace : WordTrace (prefixWord ++ tailWord_4135853) baseStart_4135853 baseEnd_4135853 := by
    simpa [prefixWord, tailWord_4135853, baseEnd_4135853] using wordTrace_append hprefix tailTrace_4135853
  have hstable : (prefixWord ++ tailWord_4135853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135853).length < 2 ^ (prefixWord ++ tailWord_4135853).sum := by decide
  have hdescent : baseEnd_4135853 < baseStart_4135853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135875 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 2, 4]
def baseStart_4135875 : Nat := 118140960795 + 4135875 * 2 ^ 59
def prefixEnd_4135875 : Nat := 4983230072969 + 3 ^ 40 * 4135875 * 2
def baseEnd_4135875 : Nat := 707897267304703701247321

theorem tailTrace_4135875 : CollatzResearch.WordTrace tailWord_4135875 prefixEnd_4135875 707897267304703701247321 := by
  unfold tailWord_4135875
  simp only [CollatzResearch.WordTrace]
  refine ⟨150847753891438701059617079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100565169260959134039744719 150847753891438701059617079)
  ·
    refine ⟨226271630837158051589425619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150847753891438701059617079 226271630837158051589425619)
    ·
      refine ⟨339407446255737077384138429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226271630837158051589425619 339407446255737077384138429)
      ·
        refine ⟨127277792345901404019051911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339407446255737077384138429 127277792345901404019051911)
        ·
          refine ⟨190916688518852106028577867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127277792345901404019051911 190916688518852106028577867)
          ·
            refine ⟨286375032778278159042866801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190916688518852106028577867 286375032778278159042866801)
            ·
              refine ⟨214781274583708619282150101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286375032778278159042866801 214781274583708619282150101)
              ·
                refine ⟨5033936123055670764425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214781274583708619282150101 5033936123055670764425393)
                ·
                  refine ⟨3775452092291753073319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033936123055670764425393 3775452092291753073319045)
                  ·
                    refine ⟨707897267304703701247321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775452092291753073319045 707897267304703701247321)
                    ·
                      rfl

theorem cell23_4135875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 4].length) (baseStart_4135875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135875 prefixEnd_4135875 := by exact prefixLift 4135875
  have htrace : WordTrace (prefixWord ++ tailWord_4135875) baseStart_4135875 baseEnd_4135875 := by
    simpa [prefixWord, tailWord_4135875, baseEnd_4135875] using wordTrace_append hprefix tailTrace_4135875
  have hstable : (prefixWord ++ tailWord_4135875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135875).length < 2 ^ (prefixWord ++ tailWord_4135875).sum := by decide
  have hdescent : baseEnd_4135875 < baseStart_4135875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135882 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_4135882 : Nat := 118140960795 + 4135882 * 2 ^ 59
def prefixEnd_4135882 : Nat := 4983230072969 + 3 ^ 40 * 4135882 * 2
def baseEnd_4135882 : Nat := 2123695396278692576354431

theorem tailTrace_4135882 : CollatzResearch.WordTrace tailWord_4135882 prefixEnd_4135882 2123695396278692576354431 := by
  unfold tailWord_4135882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37712002300603335313780475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100565339468275560836747933 37712002300603335313780475)
  ·
    refine ⟨56568003450905002970670713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37712002300603335313780475 56568003450905002970670713)
    ·
      refine ⟨42426002588178752228003035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56568003450905002970670713 42426002588178752228003035)
      ·
        refine ⟨63639003882268128342004553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42426002588178752228003035 63639003882268128342004553)
        ·
          refine ⟨47729252911701096256503415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63639003882268128342004553 47729252911701096256503415)
          ·
            refine ⟨71593879367551644384755123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47729252911701096256503415 71593879367551644384755123)
            ·
              refine ⟨107390819051327466577132685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71593879367551644384755123 107390819051327466577132685)
              ·
                refine ⟨40271557144247799966424757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107390819051327466577132685 40271557144247799966424757)
                ·
                  refine ⟨3775458482273231246852321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40271557144247799966424757 3775458482273231246852321)
                  ·
                    refine ⟨2831593861704923435139241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3775458482273231246852321 2831593861704923435139241)
                    ·
                      refine ⟨2123695396278692576354431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831593861704923435139241 2123695396278692576354431)
                      ·
                        rfl

theorem cell23_4135882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_4135882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135882 prefixEnd_4135882 := by exact prefixLift 4135882
  have htrace : WordTrace (prefixWord ++ tailWord_4135882) baseStart_4135882 baseEnd_4135882 := by
    simpa [prefixWord, tailWord_4135882, baseEnd_4135882] using wordTrace_append hprefix tailTrace_4135882
  have hstable : (prefixWord ++ tailWord_4135882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135882).length < 2 ^ (prefixWord ++ tailWord_4135882).sum := by decide
  have hdescent : baseEnd_4135882 < baseStart_4135882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135908 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4135908 : Nat := 118140960795 + 4135908 * 2 ^ 59
def prefixEnd_4135908 : Nat := 4983230072969 + 3 ^ 40 * 4135908 * 2
def baseEnd_4135908 : Nat := 2123708746775709474629311

theorem tailTrace_4135908 : CollatzResearch.WordTrace tailWord_4135908 prefixEnd_4135908 2123708746775709474629311 := by
  unfold tailWord_4135908
  simp only [CollatzResearch.WordTrace]
  refine ⟨75424478750159573847784189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100565971666879431797045585 75424478750159573847784189)
  ·
    refine ⟨28284179531309840192919071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75424478750159573847784189 28284179531309840192919071)
    ·
      refine ⟨42426269296964760289378607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28284179531309840192919071 42426269296964760289378607)
      ·
        refine ⟨63639403945447140434067911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42426269296964760289378607 63639403945447140434067911)
        ·
          refine ⟨95459105918170710651101867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63639403945447140434067911 95459105918170710651101867)
          ·
            refine ⟨143188658877256065976652801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95459105918170710651101867 143188658877256065976652801)
            ·
              refine ⟨107391494157942049482489601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143188658877256065976652801 107391494157942049482489601)
              ·
                refine ⟨80543620618456537111867201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107391494157942049482489601 80543620618456537111867201)
                ·
                  refine ⟨60407715463842402833900401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80543620618456537111867201 60407715463842402833900401)
                  ·
                    refine ⟨45305786597881802125425301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60407715463842402833900401 45305786597881802125425301)
                    ·
                      refine ⟨2123708746775709474629311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45305786597881802125425301 2123708746775709474629311)
                      ·
                        rfl

theorem cell23_4135908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4135908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135908 prefixEnd_4135908 := by exact prefixLift 4135908
  have htrace : WordTrace (prefixWord ++ tailWord_4135908) baseStart_4135908 baseEnd_4135908 := by
    simpa [prefixWord, tailWord_4135908, baseEnd_4135908] using wordTrace_append hprefix tailTrace_4135908
  have hstable : (prefixWord ++ tailWord_4135908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135908).length < 2 ^ (prefixWord ++ tailWord_4135908).sum := by decide
  have hdescent : baseEnd_4135908 < baseStart_4135908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135928 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_4135928 : Nat := 118140960795 + 4135928 * 2 ^ 59
def prefixEnd_4135928 : Nat := 4983230072969 + 3 ^ 40 * 4135928 * 2
def baseEnd_4135928 : Nat := 2123719016388799396379219

theorem tailTrace_4135928 : CollatzResearch.WordTrace tailWord_4135928 prefixEnd_4135928 2123719016388799396379219 := by
  unfold tailWord_4135928
  simp only [CollatzResearch.WordTrace]
  refine ⟨75424843480123345555648219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100566457973497794074197625 75424843480123345555648219)
  ·
    refine ⟨113137265220185018333472329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75424843480123345555648219 113137265220185018333472329)
    ·
      refine ⟨84852948915138763750104247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113137265220185018333472329 84852948915138763750104247)
      ·
        refine ⟨127279423372708145625156371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84852948915138763750104247 127279423372708145625156371)
        ·
          refine ⟨190919135059062218437734557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127279423372708145625156371 190919135059062218437734557)
          ·
            refine ⟨71594675647148331914150459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190919135059062218437734557 71594675647148331914150459)
            ·
              refine ⟨107392013470722497871225689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71594675647148331914150459 107392013470722497871225689)
              ·
                refine ⟨80544010103041873403419267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107392013470722497871225689 80544010103041873403419267)
                ·
                  refine ⟨120816015154562810105128901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80544010103041873403419267 120816015154562810105128901)
                  ·
                    refine ⟨22653002841480526894711669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120816015154562810105128901 22653002841480526894711669)
                    ·
                      refine ⟨2123719016388799396379219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22653002841480526894711669 2123719016388799396379219)
                      ·
                        rfl

theorem cell23_4135928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_4135928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135928 prefixEnd_4135928 := by exact prefixLift 4135928
  have htrace : WordTrace (prefixWord ++ tailWord_4135928) baseStart_4135928 baseEnd_4135928 := by
    simpa [prefixWord, tailWord_4135928, baseEnd_4135928] using wordTrace_append hprefix tailTrace_4135928
  have hstable : (prefixWord ++ tailWord_4135928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135928).length < 2 ^ (prefixWord ++ tailWord_4135928).sum := by decide
  have hdescent : baseEnd_4135928 < baseStart_4135928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135932 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_4135932 : Nat := 118140960795 + 4135932 * 2 ^ 59
def prefixEnd_4135932 : Nat := 4983230072969 + 3 ^ 40 * 4135932 * 2
def baseEnd_4135932 : Nat := 2123721070311417380729201

theorem tailTrace_4135932 : CollatzResearch.WordTrace tailWord_4135932 prefixEnd_4135932 2123721070311417380729201 := by
  unfold tailWord_4135932
  simp only [CollatzResearch.WordTrace]
  refine ⟨75424916426116099897221025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100566555234821466529628033 75424916426116099897221025)
  ·
    refine ⟨56568687319587074922915769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75424916426116099897221025 56568687319587074922915769)
    ·
      refine ⟨42426515489690306192186827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56568687319587074922915769 42426515489690306192186827)
      ·
        refine ⟨63639773234535459288280241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42426515489690306192186827 63639773234535459288280241)
        ·
          refine ⟨47729829925901594466210181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63639773234535459288280241 47729829925901594466210181)
          ·
            refine ⟨8949343111106548962414409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47729829925901594466210181 8949343111106548962414409)
            ·
              refine ⟨6712007333329911721810807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8949343111106548962414409 6712007333329911721810807)
              ·
                refine ⟨10068010999994867582716211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712007333329911721810807 10068010999994867582716211)
                ·
                  refine ⟨15102016499992301374074317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10068010999994867582716211 15102016499992301374074317)
                  ·
                    refine ⟨5663256187497113015277869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15102016499992301374074317 5663256187497113015277869)
                    ·
                      refine ⟨2123721070311417380729201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663256187497113015277869 2123721070311417380729201)
                      ·
                        rfl

theorem cell23_4135932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_4135932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135932 prefixEnd_4135932 := by exact prefixLift 4135932
  have htrace : WordTrace (prefixWord ++ tailWord_4135932) baseStart_4135932 baseEnd_4135932 := by
    simpa [prefixWord, tailWord_4135932, baseEnd_4135932] using wordTrace_append hprefix tailTrace_4135932
  have hstable : (prefixWord ++ tailWord_4135932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135932).length < 2 ^ (prefixWord ++ tailWord_4135932).sum := by decide
  have hdescent : baseEnd_4135932 < baseStart_4135932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135985 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4135985 : Nat := 118140960795 + 4135985 * 2 ^ 59
def prefixEnd_4135985 : Nat := 4983230072969 + 3 ^ 40 * 4135985 * 2
def baseEnd_4135985 : Nat := 2123748284786105673366457

theorem tailTrace_4135985 : CollatzResearch.WordTrace tailWord_4135985 prefixEnd_4135985 2123748284786105673366457 := by
  unfold tailWord_4135985
  simp only [CollatzResearch.WordTrace]
  refine ⟨150851765921040189846121409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100567843947360126564080939 150851765921040189846121409)
  ·
    refine ⟨113138824440780142384591057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150851765921040189846121409 113138824440780142384591057)
    ·
      refine ⟨84854118330585106788443293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113138824440780142384591057 84854118330585106788443293)
      ·
        refine ⟨31820294373969415045666235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84854118330585106788443293 31820294373969415045666235)
        ·
          refine ⟨47730441560954122568499353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31820294373969415045666235 47730441560954122568499353)
          ·
            refine ⟨35797831170715591926374515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47730441560954122568499353 35797831170715591926374515)
            ·
              refine ⟨53696746756073387889561773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35797831170715591926374515 53696746756073387889561773)
              ·
                refine ⟨20136280033527520458585665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53696746756073387889561773 20136280033527520458585665)
                ·
                  refine ⟨15102210025145640343939249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20136280033527520458585665 15102210025145640343939249)
                  ·
                    refine ⟨11326657518859230257954437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15102210025145640343939249 11326657518859230257954437)
                    ·
                      refine ⟨2123748284786105673366457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11326657518859230257954437 2123748284786105673366457)
                      ·
                        rfl

theorem cell23_4135985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4135985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4135985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4135985 prefixEnd_4135985 := by exact prefixLift 4135985
  have htrace : WordTrace (prefixWord ++ tailWord_4135985) baseStart_4135985 baseEnd_4135985 := by
    simpa [prefixWord, tailWord_4135985, baseEnd_4135985] using wordTrace_append hprefix tailTrace_4135985
  have hstable : (prefixWord ++ tailWord_4135985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135985).length < 2 ^ (prefixWord ++ tailWord_4135985).sum := by decide
  have hdescent : baseEnd_4135985 < baseStart_4135985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136005 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_4136005 : Nat := 118140960795 + 4136005 * 2 ^ 59
def prefixEnd_4136005 : Nat := 4983230072969 + 3 ^ 40 * 4136005 * 2
def baseEnd_4136005 : Nat := 2123758554399195595116365

theorem tailTrace_4136005 : CollatzResearch.WordTrace tailWord_4136005 prefixEnd_4136005 2123758554399195595116365 := by
  unfold tailWord_4136005
  simp only [CollatzResearch.WordTrace]
  refine ⟨150852495380967733261849469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100568330253978488841232979 150852495380967733261849469)
  ·
    refine ⟨56569685767862899973193551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150852495380967733261849469 56569685767862899973193551)
    ·
      refine ⟨84854528651794349959790327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56569685767862899973193551 84854528651794349959790327)
      ·
        refine ⟨127281792977691524939685491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84854528651794349959790327 127281792977691524939685491)
        ·
          refine ⟨190922689466537287409528237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127281792977691524939685491 190922689466537287409528237)
          ·
            refine ⟨71596008549951482778573089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190922689466537287409528237 71596008549951482778573089)
            ·
              refine ⟨53697006412463612083929817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71596008549951482778573089 53697006412463612083929817)
              ·
                refine ⟨40272754809347709062947363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53697006412463612083929817 40272754809347709062947363)
                ·
                  refine ⟨60409132214021563594421045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40272754809347709062947363 60409132214021563594421045)
                  ·
                    refine ⟨5663356145064521586976973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60409132214021563594421045 5663356145064521586976973)
                    ·
                      refine ⟨2123758554399195595116365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663356145064521586976973 2123758554399195595116365)
                      ·
                        rfl

theorem cell23_4136005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_4136005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136005 prefixEnd_4136005 := by exact prefixLift 4136005
  have htrace : WordTrace (prefixWord ++ tailWord_4136005) baseStart_4136005 baseEnd_4136005 := by
    simpa [prefixWord, tailWord_4136005, baseEnd_4136005] using wordTrace_append hprefix tailTrace_4136005
  have hstable : (prefixWord ++ tailWord_4136005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136005).length < 2 ^ (prefixWord ++ tailWord_4136005).sum := by decide
  have hdescent : baseEnd_4136005 < baseStart_4136005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136032 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2]
def baseStart_4136032 : Nat := 118140960795 + 4136032 * 2 ^ 59
def prefixEnd_4136032 : Nat := 4983230072969 + 3 ^ 40 * 4136032 * 2
def baseEnd_4136032 : Nat := 2123772418376866989478741

theorem tailTrace_4136032 : CollatzResearch.WordTrace tailWord_4136032 prefixEnd_4136032 2123772418376866989478741 := by
  unfold tailWord_4136032
  simp only [CollatzResearch.WordTrace]
  refine ⟨75426740075934958436541175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100568986767913277915388233 75426740075934958436541175)
  ·
    refine ⟨113140110113902437654811763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75426740075934958436541175 113140110113902437654811763)
    ·
      refine ⟨169710165170853656482217645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113140110113902437654811763 169710165170853656482217645)
      ·
        refine ⟨63641311939070121180831617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169710165170853656482217645 63641311939070121180831617)
        ·
          refine ⟨47730983954302590885623713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63641311939070121180831617 47730983954302590885623713)
          ·
            refine ⟨35798237965726943164217785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47730983954302590885623713 35798237965726943164217785)
            ·
              refine ⟨26848678474295207373163339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35798237965726943164217785 26848678474295207373163339)
              ·
                refine ⟨40273017711442811059745009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26848678474295207373163339 40273017711442811059745009)
                ·
                  refine ⟨30204763283582108294808757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40273017711442811059745009 30204763283582108294808757)
                  ·
                    refine ⟨2831696557835822652638321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30204763283582108294808757 2831696557835822652638321)
                    ·
                      refine ⟨2123772418376866989478741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831696557835822652638321 2123772418376866989478741)
                      ·
                        rfl

theorem cell23_4136032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_4136032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136032 prefixEnd_4136032 := by exact prefixLift 4136032
  have htrace : WordTrace (prefixWord ++ tailWord_4136032) baseStart_4136032 baseEnd_4136032 := by
    simpa [prefixWord, tailWord_4136032, baseEnd_4136032] using wordTrace_append hprefix tailTrace_4136032
  have hstable : (prefixWord ++ tailWord_4136032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136032).length < 2 ^ (prefixWord ++ tailWord_4136032).sum := by decide
  have hdescent : baseEnd_4136032 < baseStart_4136032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136106 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4136106 : Nat := 118140960795 + 4136106 * 2 ^ 59
def prefixEnd_4136106 : Nat := 4983230072969 + 3 ^ 40 * 4136106 * 2
def baseEnd_4136106 : Nat := 707936805315099899984467

theorem tailTrace_4136106 : CollatzResearch.WordTrace tailWord_4136106 prefixEnd_4136106 707936805315099899984467 := by
  unfold tailWord_4136106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37714044788400456877819043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100570786102401218340850781 37714044788400456877819043)
  ·
    refine ⟨56571067182600685316728565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37714044788400456877819043 56571067182600685316728565)
    ·
      refine ⟨5303537548368814248443303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56571067182600685316728565 5303537548368814248443303)
      ·
        refine ⟨7955306322553221372664955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303537548368814248443303 7955306322553221372664955)
        ·
          refine ⟨11932959483829832058997433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955306322553221372664955 11932959483829832058997433)
          ·
            refine ⟨8949719612872374044248075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11932959483829832058997433 8949719612872374044248075)
            ·
              refine ⟨13424579419308561066372113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8949719612872374044248075 13424579419308561066372113)
              ·
                refine ⟨10068434564481420799779085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13424579419308561066372113 10068434564481420799779085)
                ·
                  refine ⟨3775662961680532799917157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10068434564481420799779085 3775662961680532799917157)
                  ·
                    refine ⟨707936805315099899984467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775662961680532799917157 707936805315099899984467)
                    ·
                      rfl

theorem cell23_4136106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4136106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136106 prefixEnd_4136106 := by exact prefixLift 4136106
  have htrace : WordTrace (prefixWord ++ tailWord_4136106) baseStart_4136106 baseEnd_4136106 := by
    simpa [prefixWord, tailWord_4136106, baseEnd_4136106] using wordTrace_append hprefix tailTrace_4136106
  have hstable : (prefixWord ++ tailWord_4136106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136106).length < 2 ^ (prefixWord ++ tailWord_4136106).sum := by decide
  have hdescent : baseEnd_4136106 < baseStart_4136106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136146 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4136146 : Nat := 118140960795 + 4136146 * 2 ^ 59
def prefixEnd_4136146 : Nat := 4983230072969 + 3 ^ 40 * 4136146 * 2
def baseEnd_4136146 : Nat := 2123830955171479543453217

theorem tailTrace_4136146 : CollatzResearch.WordTrace tailWord_4136146 prefixEnd_4136146 2123830955171479543453217 := by
  unfold tailWord_4136146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37714409518364228585683073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100571758715637942895154861 37714409518364228585683073)
  ·
    refine ⟨28285807138773171439262305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37714409518364228585683073 28285807138773171439262305)
    ·
      refine ⟨21214355354079878579446729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28285807138773171439262305 21214355354079878579446729)
      ·
        refine ⟨15910766515559908934585047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21214355354079878579446729 15910766515559908934585047)
        ·
          refine ⟨23866149773339863401877571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15910766515559908934585047 23866149773339863401877571)
          ·
            refine ⟨35799224660009795102816357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23866149773339863401877571 35799224660009795102816357)
            ·
              refine ⟨6712354623751836581778067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35799224660009795102816357 6712354623751836581778067)
              ·
                refine ⟨10068531935627754872667101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712354623751836581778067 10068531935627754872667101)
                ·
                  refine ⟨3775699475860408077250163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10068531935627754872667101 3775699475860408077250163)
                  ·
                    refine ⟨5663549213790612115875245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3775699475860408077250163 5663549213790612115875245)
                    ·
                      refine ⟨2123830955171479543453217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663549213790612115875245 2123830955171479543453217)
                      ·
                        rfl

theorem cell23_4136146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4136146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136146 prefixEnd_4136146 := by exact prefixLift 4136146
  have htrace : WordTrace (prefixWord ++ tailWord_4136146) baseStart_4136146 baseEnd_4136146 := by
    simpa [prefixWord, tailWord_4136146, baseEnd_4136146] using wordTrace_append hprefix tailTrace_4136146
  have hstable : (prefixWord ++ tailWord_4136146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136146).length < 2 ^ (prefixWord ++ tailWord_4136146).sum := by decide
  have hdescent : baseEnd_4136146 < baseStart_4136146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136155 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_4136155 : Nat := 118140960795 + 4136155 * 2 ^ 59
def prefixEnd_4136155 : Nat := 4983230072969 + 3 ^ 40 * 4136155 * 2
def baseEnd_4136155 : Nat := 2123835576497370008240675

theorem tailTrace_4136155 : CollatzResearch.WordTrace tailWord_4136155 prefixEnd_4136155 2123835576497370008240675 := by
  unfold tailWord_4136155
  simp only [CollatzResearch.WordTrace]
  refine ⟨150857966330424308879809919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100571977553616205919873279 150857966330424308879809919)
  ·
    refine ⟨226286949495636463319714879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150857966330424308879809919 226286949495636463319714879)
    ·
      refine ⟨339430424243454694979572319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226286949495636463319714879 339430424243454694979572319)
      ·
        refine ⟨509145636365182042469358479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339430424243454694979572319 509145636365182042469358479)
        ·
          refine ⟨763718454547773063704037719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509145636365182042469358479 763718454547773063704037719)
          ·
            refine ⟨1145577681821659595556056579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763718454547773063704037719 1145577681821659595556056579)
            ·
              refine ⟨1718366522732489393334084869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145577681821659595556056579 1718366522732489393334084869)
              ·
                refine ⟨322193723012341761250140913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1718366522732489393334084869 322193723012341761250140913)
                ·
                  refine ⟨241645292259256320937605685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322193723012341761250140913 241645292259256320937605685)
                  ·
                    refine ⟨22654246149305280087900533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241645292259256320937605685 22654246149305280087900533)
                    ·
                      refine ⟨2123835576497370008240675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22654246149305280087900533 2123835576497370008240675)
                      ·
                        rfl

theorem cell23_4136155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_4136155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136155 prefixEnd_4136155 := by exact prefixLift 4136155
  have htrace : WordTrace (prefixWord ++ tailWord_4136155) baseStart_4136155 baseEnd_4136155 := by
    simpa [prefixWord, tailWord_4136155, baseEnd_4136155] using wordTrace_append hprefix tailTrace_4136155
  have hstable : (prefixWord ++ tailWord_4136155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136155).length < 2 ^ (prefixWord ++ tailWord_4136155).sum := by decide
  have hdescent : baseEnd_4136155 < baseStart_4136155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136203 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 3, 2, 2]
def baseStart_4136203 : Nat := 118140960795 + 4136203 * 2 ^ 59
def prefixEnd_4136203 : Nat := 4983230072969 + 3 ^ 40 * 4136203 * 2
def baseEnd_4136203 : Nat := 2123860223568785820440455

theorem tailTrace_4136203 : CollatzResearch.WordTrace tailWord_4136203 prefixEnd_4136203 2123860223568785820440455 := by
  unfold tailWord_4136203
  simp only [CollatzResearch.WordTrace]
  refine ⟨150859717034250413077557263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100573144689500275385038175 150859717034250413077557263)
  ·
    refine ⟨226289575551375619616335895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150859717034250413077557263 226289575551375619616335895)
    ·
      refine ⟨339434363327063429424503843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226289575551375619616335895 339434363327063429424503843)
      ·
        refine ⟨509151544990595144136755765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339434363327063429424503843 509151544990595144136755765)
        ·
          refine ⟨47732957342868294762820853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 509151544990595144136755765 47732957342868294762820853)
          ·
            refine ⟨4474964750893902634014455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47732957342868294762820853 4474964750893902634014455)
            ·
              refine ⟨6712447126340853951021683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474964750893902634014455 6712447126340853951021683)
              ·
                refine ⟨10068670689511280926532525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712447126340853951021683 10068670689511280926532525)
                ·
                  refine ⟨3775751508566730347449697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10068670689511280926532525 3775751508566730347449697)
                  ·
                    refine ⟨2831813631425047760587273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3775751508566730347449697 2831813631425047760587273)
                    ·
                      refine ⟨2123860223568785820440455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831813631425047760587273 2123860223568785820440455)
                      ·
                        rfl

theorem cell23_4136203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2, 2].length) (baseStart_4136203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136203 prefixEnd_4136203 := by exact prefixLift 4136203
  have htrace : WordTrace (prefixWord ++ tailWord_4136203) baseStart_4136203 baseEnd_4136203 := by
    simpa [prefixWord, tailWord_4136203, baseEnd_4136203] using wordTrace_append hprefix tailTrace_4136203
  have hstable : (prefixWord ++ tailWord_4136203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136203).length < 2 ^ (prefixWord ++ tailWord_4136203).sum := by decide
  have hdescent : baseEnd_4136203 < baseStart_4136203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136223 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_4136223 : Nat := 118140960795 + 4136223 * 2 ^ 59
def prefixEnd_4136223 : Nat := 4983230072969 + 3 ^ 40 * 4136223 * 2
def baseEnd_4136223 : Nat := 2123870493181875742190363

theorem tailTrace_4136223 : CollatzResearch.WordTrace tailWord_4136223 prefixEnd_4136223 2123870493181875742190363 := by
  unfold tailWord_4136223
  simp only [CollatzResearch.WordTrace]
  refine ⟨150860446494177956493285323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100573630996118637662190215 150860446494177956493285323)
  ·
    refine ⟨226290669741266934739927985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150860446494177956493285323 226290669741266934739927985)
    ·
      refine ⟨169718002305950201054945989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226290669741266934739927985 169718002305950201054945989)
      ·
        refine ⟨31822125432365662697802373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169718002305950201054945989 31822125432365662697802373)
        ·
          refine ⟨5966648518568561755837945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31822125432365662697802373 5966648518568561755837945)
          ·
            refine ⟨4474986388926421316878459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5966648518568561755837945 4474986388926421316878459)
            ·
              refine ⟨6712479583389631975317689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474986388926421316878459 6712479583389631975317689)
              ·
                refine ⟨5034359687542223981488267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6712479583389631975317689 5034359687542223981488267)
                ·
                  refine ⟨7551539531313335972232401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034359687542223981488267 7551539531313335972232401)
                  ·
                    refine ⟨5663654648485001979174301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7551539531313335972232401 5663654648485001979174301)
                    ·
                      refine ⟨2123870493181875742190363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663654648485001979174301 2123870493181875742190363)
                      ·
                        rfl

theorem cell23_4136223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_4136223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136223 prefixEnd_4136223 := by exact prefixLift 4136223
  have htrace : WordTrace (prefixWord ++ tailWord_4136223) baseStart_4136223 baseEnd_4136223 := by
    simpa [prefixWord, tailWord_4136223, baseEnd_4136223] using wordTrace_append hprefix tailTrace_4136223
  have hstable : (prefixWord ++ tailWord_4136223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136223).length < 2 ^ (prefixWord ++ tailWord_4136223).sum := by decide
  have hdescent : baseEnd_4136223 < baseStart_4136223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136259 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 5, 4, 2]
def baseStart_4136259 : Nat := 118140960795 + 4136259 * 2 ^ 59
def prefixEnd_4136259 : Nat := 4983230072969 + 3 ^ 40 * 4136259 * 2
def baseEnd_4136259 : Nat := 2123888978485437601340197

theorem tailTrace_4136259 : CollatzResearch.WordTrace tailWord_4136259 prefixEnd_4136259 2123888978485437601340197 := by
  unfold tailWord_4136259
  simp only [CollatzResearch.WordTrace]
  refine ⟨150861759522047534641595831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100574506348031689761063887 150861759522047534641595831)
  ·
    refine ⟨226292639283071301962393747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150861759522047534641595831 226292639283071301962393747)
    ·
      refine ⟨339438958924606952943590621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226292639283071301962393747 339438958924606952943590621)
      ·
        refine ⟨127289609596727607353846483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339438958924606952943590621 127289609596727607353846483)
        ·
          refine ⟨190934414395091411030769725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127289609596727607353846483 190934414395091411030769725)
          ·
            refine ⟨71600405398159279136538647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190934414395091411030769725 71600405398159279136538647)
            ·
              refine ⟨107400608097238918704807971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71600405398159279136538647 107400608097238918704807971)
              ·
                refine ⟨161100912145858378057211957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107400608097238918704807971 161100912145858378057211957)
                ·
                  refine ⟨15103210513674222942863621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161100912145858378057211957 15103210513674222942863621)
                  ·
                    refine ⟨2831851971313916801786929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15103210513674222942863621 2831851971313916801786929)
                    ·
                      refine ⟨2123888978485437601340197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2831851971313916801786929 2123888978485437601340197)
                      ·
                        rfl

theorem cell23_4136259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_4136259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136259 prefixEnd_4136259 := by exact prefixLift 4136259
  have htrace : WordTrace (prefixWord ++ tailWord_4136259) baseStart_4136259 baseEnd_4136259 := by
    simpa [prefixWord, tailWord_4136259, baseEnd_4136259] using wordTrace_append hprefix tailTrace_4136259
  have hstable : (prefixWord ++ tailWord_4136259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136259).length < 2 ^ (prefixWord ++ tailWord_4136259).sum := by decide
  have hdescent : baseEnd_4136259 < baseStart_4136259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136282 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_4136282 : Nat := 118140960795 + 4136282 * 2 ^ 59
def prefixEnd_4136282 : Nat := 4983230072969 + 3 ^ 40 * 4136282 * 2
def baseEnd_4136282 : Nat := 235988976504499001261399

theorem tailTrace_4136282 : CollatzResearch.WordTrace tailWord_4136282 prefixEnd_4136282 235988976504499001261399 := by
  unfold tailWord_4136282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37715649600241052392420775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100575065600642806379788733 37715649600241052392420775)
  ·
    refine ⟨56573474400361578588631163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37715649600241052392420775 56573474400361578588631163)
    ·
      refine ⟨84860211600542367882946745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56573474400361578588631163 84860211600542367882946745)
      ·
        refine ⟨63645158700406775912210059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84860211600542367882946745 63645158700406775912210059)
        ·
          refine ⟨95467738050610163868315089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63645158700406775912210059 95467738050610163868315089)
          ·
            refine ⟨71600803537957622901236317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95467738050610163868315089 71600803537957622901236317)
            ·
              refine ⟨26850301326734108587963619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71600803537957622901236317 26850301326734108587963619)
              ·
                refine ⟨40275451990101162881945429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26850301326734108587963619 40275451990101162881945429)
                ·
                  refine ⟨235988976504499001261399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40275451990101162881945429 235988976504499001261399)
                  ·
                    rfl

theorem cell23_4136282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_4136282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136282 prefixEnd_4136282 := by exact prefixLift 4136282
  have htrace : WordTrace (prefixWord ++ tailWord_4136282) baseStart_4136282 baseEnd_4136282 := by
    simpa [prefixWord, tailWord_4136282, baseEnd_4136282] using wordTrace_append hprefix tailTrace_4136282
  have hstable : (prefixWord ++ tailWord_4136282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136282).length < 2 ^ (prefixWord ++ tailWord_4136282).sum := by decide
  have hdescent : baseEnd_4136282 < baseStart_4136282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136376 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_4136376 : Nat := 118140960795 + 4136376 * 2 ^ 59
def prefixEnd_4136376 : Nat := 4983230072969 + 3 ^ 40 * 4136376 * 2
def baseEnd_4136376 : Nat := 707983018574004547859053

theorem tailTrace_4136376 : CollatzResearch.WordTrace tailWord_4136376 prefixEnd_4136376 707983018574004547859053 := by
  unfold tailWord_4136376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75433013431311831811802491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100577351241749109082403321 75433013431311831811802491)
  ·
    refine ⟨113149520146967747717703737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75433013431311831811802491 113149520146967747717703737)
    ·
      refine ⟨84862140110225810788277803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113149520146967747717703737 84862140110225810788277803)
      ·
        refine ⟨127293210165338716182416705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84862140110225810788277803 127293210165338716182416705)
        ·
          refine ⟨95469907624004037136812529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127293210165338716182416705 95469907624004037136812529)
          ·
            refine ⟨71602430718003027852609397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95469907624004037136812529 71602430718003027852609397)
            ·
              refine ⟨6712727879812783861182131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71602430718003027852609397 6712727879812783861182131)
              ·
                refine ⟨10069091819719175791773197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712727879812783861182131 10069091819719175791773197)
                ·
                  refine ⟨3775909432394690921914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10069091819719175791773197 3775909432394690921914949)
                  ·
                    refine ⟨707983018574004547859053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775909432394690921914949 707983018574004547859053)
                    ·
                      rfl

theorem cell23_4136376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_4136376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136376 prefixEnd_4136376 := by exact prefixLift 4136376
  have htrace : WordTrace (prefixWord ++ tailWord_4136376) baseStart_4136376 baseEnd_4136376 := by
    simpa [prefixWord, tailWord_4136376, baseEnd_4136376] using wordTrace_append hprefix tailTrace_4136376
  have hstable : (prefixWord ++ tailWord_4136376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136376).length < 2 ^ (prefixWord ++ tailWord_4136376).sum := by decide
  have hdescent : baseEnd_4136376 < baseStart_4136376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136399 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_4136399 : Nat := 118140960795 + 4136399 * 2 ^ 59
def prefixEnd_4136399 : Nat := 4983230072969 + 3 ^ 40 * 4136399 * 2
def baseEnd_4136399 : Nat := 2123960865777067053589553

theorem tailTrace_4136399 : CollatzResearch.WordTrace tailWord_4136399 prefixEnd_4136399 2123960865777067053589553 := by
  unfold tailWord_4136399
  simp only [CollatzResearch.WordTrace]
  refine ⟨150866865741540338551692251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100577910494360225701128167 150866865741540338551692251)
  ·
    refine ⟨226300298612310507827538377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150866865741540338551692251 226300298612310507827538377)
    ·
      refine ⟨169725223959232880870653783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226300298612310507827538377 169725223959232880870653783)
      ·
        refine ⟨254587835938849321305980675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169725223959232880870653783 254587835938849321305980675)
        ·
          refine ⟨381881753908273981958971013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254587835938849321305980675 381881753908273981958971013)
          ·
            refine ⟨71602828857801371617307065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381881753908273981958971013 71602828857801371617307065)
            ·
              refine ⟨53702121643351028712980299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71602828857801371617307065 53702121643351028712980299)
              ·
                refine ⟨80553182465026543069470449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53702121643351028712980299 80553182465026543069470449)
                ·
                  refine ⟨60414886848769907302102837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80553182465026543069470449 60414886848769907302102837)
                  ·
                    refine ⟨5663895642072178809572141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60414886848769907302102837 5663895642072178809572141)
                    ·
                      refine ⟨2123960865777067053589553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663895642072178809572141 2123960865777067053589553)
                      ·
                        rfl

theorem cell23_4136399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_4136399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136399 prefixEnd_4136399 := by exact prefixLift 4136399
  have htrace : WordTrace (prefixWord ++ tailWord_4136399) baseStart_4136399 baseEnd_4136399 := by
    simpa [prefixWord, tailWord_4136399, baseEnd_4136399] using wordTrace_append hprefix tailTrace_4136399
  have hstable : (prefixWord ++ tailWord_4136399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136399).length < 2 ^ (prefixWord ++ tailWord_4136399).sum := by decide
  have hdescent : baseEnd_4136399 < baseStart_4136399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136416 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3]
def baseStart_4136416 : Nat := 118140960795 + 4136416 * 2 ^ 59
def prefixEnd_4136416 : Nat := 4983230072969 + 3 ^ 40 * 4136416 * 2
def baseEnd_4136416 : Nat := 2123969594948193487076975

theorem tailTrace_4136416 : CollatzResearch.WordTrace tailWord_4136416 prefixEnd_4136416 2123969594948193487076975 := by
  unfold tailWord_4136416
  simp only [CollatzResearch.WordTrace]
  refine ⟨75433742891239375227530551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100578323854985833636707401 75433742891239375227530551)
  ·
    refine ⟨113150614336859062841295827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75433742891239375227530551 113150614336859062841295827)
    ·
      refine ⟨169725921505288594261943741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113150614336859062841295827 169725921505288594261943741)
      ·
        refine ⟨63647220564483222848228903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169725921505288594261943741 63647220564483222848228903)
        ·
          refine ⟨95470830846724834272343355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63647220564483222848228903 95470830846724834272343355)
          ·
            refine ⟨143206246270087251408515033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95470830846724834272343355 143206246270087251408515033)
            ·
              refine ⟨107404684702565438556386275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143206246270087251408515033 107404684702565438556386275)
              ·
                refine ⟨161107027053848157834579413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107404684702565438556386275 161107027053848157834579413)
                ·
                  refine ⟨3775945946574566199247955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161107027053848157834579413 3775945946574566199247955)
                  ·
                    refine ⟨5663918919861849298871933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3775945946574566199247955 5663918919861849298871933)
                    ·
                      refine ⟨2123969594948193487076975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663918919861849298871933 2123969594948193487076975)
                      ·
                        rfl

theorem cell23_4136416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_4136416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136416 prefixEnd_4136416 := by exact prefixLift 4136416
  have htrace : WordTrace (prefixWord ++ tailWord_4136416) baseStart_4136416 baseEnd_4136416 := by
    simpa [prefixWord, tailWord_4136416, baseEnd_4136416] using wordTrace_append hprefix tailTrace_4136416
  have hstable : (prefixWord ++ tailWord_4136416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136416).length < 2 ^ (prefixWord ++ tailWord_4136416).sum := by decide
  have hdescent : baseEnd_4136416 < baseStart_4136416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136450 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4136450 : Nat := 118140960795 + 4136450 * 2 ^ 59
def prefixEnd_4136450 : Nat := 4983230072969 + 3 ^ 40 * 4136450 * 2
def baseEnd_4136450 : Nat := 2123987053290446354051819

theorem tailTrace_4136450 : CollatzResearch.WordTrace tailWord_4136450 prefixEnd_4136450 2123987053290446354051819 := by
  unfold tailWord_4136450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717181466088893565449701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100579150576237049507865869 37717181466088893565449701)
  ·
    refine ⟨7071971524891667543521819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37717181466088893565449701 7071971524891667543521819)
    ·
      refine ⟨10607957287337501315282729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7071971524891667543521819 10607957287337501315282729)
      ·
        refine ⟨7955967965503125986462047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10607957287337501315282729 7955967965503125986462047)
        ·
          refine ⟨11933951948254688979693071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955967965503125986462047 11933951948254688979693071)
          ·
            refine ⟨17900927922382033469539607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933951948254688979693071 17900927922382033469539607)
            ·
              refine ⟨26851391883573050204309411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17900927922382033469539607 26851391883573050204309411)
              ·
                refine ⟨40277087825359575306464117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26851391883573050204309411 40277087825359575306464117)
                ·
                  refine ⟨3775976983627460184981011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40277087825359575306464117 3775976983627460184981011)
                  ·
                    refine ⟨5663965475441190277471517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3775976983627460184981011 5663965475441190277471517)
                    ·
                      refine ⟨2123987053290446354051819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5663965475441190277471517 2123987053290446354051819)
                      ·
                        rfl

theorem cell23_4136450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4136450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136450 prefixEnd_4136450 := by exact prefixLift 4136450
  have htrace : WordTrace (prefixWord ++ tailWord_4136450) baseStart_4136450 baseEnd_4136450 := by
    simpa [prefixWord, tailWord_4136450, baseEnd_4136450] using wordTrace_append hprefix tailTrace_4136450
  have hstable : (prefixWord ++ tailWord_4136450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136450).length < 2 ^ (prefixWord ++ tailWord_4136450).sum := by decide
  have hdescent : baseEnd_4136450 < baseStart_4136450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136456 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_4136456 : Nat := 118140960795 + 4136456 * 2 ^ 59
def prefixEnd_4136456 : Nat := 4983230072969 + 3 ^ 40 * 4136456 * 2
def baseEnd_4136456 : Nat := 2123990134174373330576791

theorem tailTrace_4136456 : CollatzResearch.WordTrace tailWord_4136456 prefixEnd_4136456 2123990134174373330576791 := by
  unfold tailWord_4136456
  simp only [CollatzResearch.WordTrace]
  refine ⟨75434472351166918643258611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100579296468222558191011481 75434472351166918643258611)
  ·
    refine ⟨113151708526750377964887917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75434472351166918643258611 113151708526750377964887917)
    ·
      refine ⟨42431890697531391736832969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113151708526750377964887917 42431890697531391736832969)
      ·
        refine ⟨31823918023148543802624727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42431890697531391736832969 31823918023148543802624727)
        ·
          refine ⟨47735877034722815703937091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31823918023148543802624727 47735877034722815703937091)
          ·
            refine ⟨71603815552084223555905637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47735877034722815703937091 71603815552084223555905637)
            ·
              refine ⟨13425715416015791916732307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71603815552084223555905637 13425715416015791916732307)
              ·
                refine ⟨20138573124023687875098461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425715416015791916732307 20138573124023687875098461)
                ·
                  refine ⟨7551964921508882953161923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20138573124023687875098461 7551964921508882953161923)
                  ·
                    refine ⟨11327947382263324429742885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7551964921508882953161923 11327947382263324429742885)
                    ·
                      refine ⟨2123990134174373330576791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11327947382263324429742885 2123990134174373330576791)
                      ·
                        rfl

theorem cell23_4136456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_4136456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136456 prefixEnd_4136456 := by exact prefixLift 4136456
  have htrace : WordTrace (prefixWord ++ tailWord_4136456) baseStart_4136456 baseEnd_4136456 := by
    simpa [prefixWord, tailWord_4136456, baseEnd_4136456] using wordTrace_append hprefix tailTrace_4136456
  have hstable : (prefixWord ++ tailWord_4136456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136456).length < 2 ^ (prefixWord ++ tailWord_4136456).sum := by decide
  have hdescent : baseEnd_4136456 < baseStart_4136456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136476 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4136476 : Nat := 118140960795 + 4136476 * 2 ^ 59
def prefixEnd_4136476 : Nat := 4983230072969 + 3 ^ 40 * 4136476 * 2
def baseEnd_4136476 : Nat := 2124000403787463252326699

theorem tailTrace_4136476 : CollatzResearch.WordTrace tailWord_4136476 prefixEnd_4136476 2124000403787463252326699 := by
  unfold tailWord_4136476
  simp only [CollatzResearch.WordTrace]
  refine ⟨75434837081130690351122641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100579782774840920468163521 75434837081130690351122641)
  ·
    refine ⟨56576127810848017763341981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75434837081130690351122641 56576127810848017763341981)
    ·
      refine ⟨21216047929068006661253243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56576127810848017763341981 21216047929068006661253243)
      ·
        refine ⟨31824071893602009991879865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216047929068006661253243 31824071893602009991879865)
        ·
          refine ⟨23868053920201507493909899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31824071893602009991879865 23868053920201507493909899)
          ·
            refine ⟨35802080880302261240864849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23868053920201507493909899 35802080880302261240864849)
            ·
              refine ⟨26851560660226695930648637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35802080880302261240864849 26851560660226695930648637)
              ·
                refine ⟨10069335247585010973993239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26851560660226695930648637 10069335247585010973993239)
                ·
                  refine ⟨15104002871377516460989859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10069335247585010973993239 15104002871377516460989859)
                  ·
                    refine ⟨22656004307066274691484789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15104002871377516460989859 22656004307066274691484789)
                    ·
                      refine ⟨2124000403787463252326699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22656004307066274691484789 2124000403787463252326699)
                      ·
                        rfl

theorem cell23_4136476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4136476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136476 prefixEnd_4136476 := by exact prefixLift 4136476
  have htrace : WordTrace (prefixWord ++ tailWord_4136476) baseStart_4136476 baseEnd_4136476 := by
    simpa [prefixWord, tailWord_4136476, baseEnd_4136476] using wordTrace_append hprefix tailTrace_4136476
  have hstable : (prefixWord ++ tailWord_4136476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136476).length < 2 ^ (prefixWord ++ tailWord_4136476).sum := by decide
  have hdescent : baseEnd_4136476 < baseStart_4136476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136483 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 4, 4]
def baseStart_4136483 : Nat := 118140960795 + 4136483 * 2 ^ 59
def prefixEnd_4136483 : Nat := 4983230072969 + 3 ^ 40 * 4136483 * 2
def baseEnd_4136483 : Nat := 708001332717348241646389

theorem tailTrace_4136483 : CollatzResearch.WordTrace tailWord_4136483 prefixEnd_4136483 708001332717348241646389 := by
  unfold tailWord_4136483
  simp only [CollatzResearch.WordTrace]
  refine ⟨150869929473236020897750103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100579952982157347265166735 150869929473236020897750103)
  ·
    refine ⟨226304894209854031346625155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150869929473236020897750103 226304894209854031346625155)
    ·
      refine ⟨339457341314781047019937733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226304894209854031346625155 339457341314781047019937733)
      ·
        refine ⟨63648251496521446316238325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339457341314781047019937733 63648251496521446316238325)
        ·
          refine ⟨5967023577798885592147343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63648251496521446316238325 5967023577798885592147343)
          ·
            refine ⟨8950535366698328388221015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967023577798885592147343 8950535366698328388221015)
            ·
              refine ⟨13425803050047492582331523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950535366698328388221015 13425803050047492582331523)
              ·
                refine ⟨20138704575071238873497285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425803050047492582331523 20138704575071238873497285)
                ·
                  refine ⟨3776007107825857288780741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20138704575071238873497285 3776007107825857288780741)
                  ·
                    refine ⟨708001332717348241646389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3776007107825857288780741 708001332717348241646389)
                    ·
                      rfl

theorem cell23_4136483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 4].length) (baseStart_4136483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136483 prefixEnd_4136483 := by exact prefixLift 4136483
  have htrace : WordTrace (prefixWord ++ tailWord_4136483) baseStart_4136483 baseEnd_4136483 := by
    simpa [prefixWord, tailWord_4136483, baseEnd_4136483] using wordTrace_append hprefix tailTrace_4136483
  have hstable : (prefixWord ++ tailWord_4136483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136483).length < 2 ^ (prefixWord ++ tailWord_4136483).sum := by decide
  have hdescent : baseEnd_4136483 < baseStart_4136483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136503 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_4136503 : Nat := 118140960795 + 4136503 * 2 ^ 59
def prefixEnd_4136503 : Nat := 4983230072969 + 3 ^ 40 * 4136503 * 2
def baseEnd_4136503 : Nat := 2124014267765134646689075

theorem tailTrace_4136503 : CollatzResearch.WordTrace tailWord_4136503 prefixEnd_4136503 2124014267765134646689075 := by
  unfold tailWord_4136503
  simp only [CollatzResearch.WordTrace]
  refine ⟨150870658933163564313478163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100580439288775709542318775 150870658933163564313478163)
  ·
    refine ⟨226305988399745346470217245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150870658933163564313478163 226305988399745346470217245)
    ·
      refine ⟨84864745649904504926331467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226305988399745346470217245 84864745649904504926331467)
      ·
        refine ⟨127297118474856757389497201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84864745649904504926331467 127297118474856757389497201)
        ·
          refine ⟨95472838856142568042122901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127297118474856757389497201 95472838856142568042122901)
          ·
            refine ⟨4475289321381682876974511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95472838856142568042122901 4475289321381682876974511)
            ·
              refine ⟨6712933982072524315461767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475289321381682876974511 6712933982072524315461767)
              ·
                refine ⟨10069400973108786473192651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712933982072524315461767 10069400973108786473192651)
                ·
                  refine ⟨15104101459663179709788977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10069400973108786473192651 15104101459663179709788977)
                  ·
                    refine ⟨11328076094747384782341733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15104101459663179709788977 11328076094747384782341733)
                    ·
                      refine ⟨2124014267765134646689075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11328076094747384782341733 2124014267765134646689075)
                      ·
                        rfl

theorem cell23_4136503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_4136503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136503 prefixEnd_4136503 := by exact prefixLift 4136503
  have htrace : WordTrace (prefixWord ++ tailWord_4136503) baseStart_4136503 baseEnd_4136503 := by
    simpa [prefixWord, tailWord_4136503, baseEnd_4136503] using wordTrace_append hprefix tailTrace_4136503
  have hstable : (prefixWord ++ tailWord_4136503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136503).length < 2 ^ (prefixWord ++ tailWord_4136503).sum := by decide
  have hdescent : baseEnd_4136503 < baseStart_4136503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136518 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4136518 : Nat := 118140960795 + 4136518 * 2 ^ 59
def prefixEnd_4136518 : Nat := 4983230072969 + 3 ^ 40 * 4136518 * 2
def baseEnd_4136518 : Nat := 2124021969974952088001507

theorem tailTrace_4136518 : CollatzResearch.WordTrace tailWord_4136518 prefixEnd_4136518 2124021969974952088001507 := by
  unfold tailWord_4136518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714725188378413183602319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100580804018739481250182805 4714725188378413183602319)
  ·
    refine ⟨7072087782567619775403479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4714725188378413183602319 7072087782567619775403479)
    ·
      refine ⟨10608131673851429663105219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7072087782567619775403479 10608131673851429663105219)
      ·
        refine ⟨15912197510777144494657829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608131673851429663105219 15912197510777144494657829)
        ·
          refine ⟨2983537033270714592748343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15912197510777144494657829 2983537033270714592748343)
          ·
            refine ⟨4475305549906071889122515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983537033270714592748343 4475305549906071889122515)
            ·
              refine ⟨6712958324859107833683773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475305549906071889122515 6712958324859107833683773)
              ·
                refine ⟨2517359371822165437631415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6712958324859107833683773 2517359371822165437631415)
                ·
                  refine ⟨3776039057733248156447123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517359371822165437631415 3776039057733248156447123)
                  ·
                    refine ⟨5664058586599872234670685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776039057733248156447123 5664058586599872234670685)
                    ·
                      refine ⟨2124021969974952088001507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664058586599872234670685 2124021969974952088001507)
                      ·
                        rfl

theorem cell23_4136518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4136518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136518 prefixEnd_4136518 := by exact prefixLift 4136518
  have htrace : WordTrace (prefixWord ++ tailWord_4136518) baseStart_4136518 baseEnd_4136518 := by
    simpa [prefixWord, tailWord_4136518, baseEnd_4136518] using wordTrace_append hprefix tailTrace_4136518
  have hstable : (prefixWord ++ tailWord_4136518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136518).length < 2 ^ (prefixWord ++ tailWord_4136518).sum := by decide
  have hdescent : baseEnd_4136518 < baseStart_4136518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136524 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4136524 : Nat := 118140960795 + 4136524 * 2 ^ 59
def prefixEnd_4136524 : Nat := 4983230072969 + 3 ^ 40 * 4136524 * 2
def baseEnd_4136524 : Nat := 2124025050858879064526479

theorem tailTrace_4136524 : CollatzResearch.WordTrace tailWord_4136524 prefixEnd_4136524 2124025050858879064526479 := by
  unfold tailWord_4136524
  simp only [CollatzResearch.WordTrace]
  refine ⟨75435712433043742449996313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100580949910724989933328417 75435712433043742449996313)
  ·
    refine ⟨56576784324782806837497235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75435712433043742449996313 56576784324782806837497235)
    ·
      refine ⟨84865176487174210256245853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56576784324782806837497235 84865176487174210256245853)
      ·
        refine ⟨31824441182690328846092195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84865176487174210256245853 31824441182690328846092195)
        ·
          refine ⟨47736661774035493269138293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31824441182690328846092195 47736661774035493269138293)
          ·
            refine ⟨4475312041315827493981715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47736661774035493269138293 4475312041315827493981715)
            ·
              refine ⟨6712968061973741240972573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475312041315827493981715 6712968061973741240972573)
              ·
                refine ⟨2517363023240152965364715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6712968061973741240972573 2517363023240152965364715)
                ·
                  refine ⟨3776044534860229448047073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517363023240152965364715 3776044534860229448047073)
                  ·
                    refine ⟨2832033401145172086035305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776044534860229448047073 2832033401145172086035305)
                    ·
                      refine ⟨2124025050858879064526479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832033401145172086035305 2124025050858879064526479)
                      ·
                        rfl

theorem cell23_4136524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4136524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136524 prefixEnd_4136524 := by exact prefixLift 4136524
  have htrace : WordTrace (prefixWord ++ tailWord_4136524) baseStart_4136524 baseEnd_4136524 := by
    simpa [prefixWord, tailWord_4136524, baseEnd_4136524] using wordTrace_append hprefix tailTrace_4136524
  have hstable : (prefixWord ++ tailWord_4136524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136524).length < 2 ^ (prefixWord ++ tailWord_4136524).sum := by decide
  have hdescent : baseEnd_4136524 < baseStart_4136524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136533 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_4136533 : Nat := 118140960795 + 4136533 * 2 ^ 59
def prefixEnd_4136533 : Nat := 4983230072969 + 3 ^ 40 * 4136533 * 2
def baseEnd_4136533 : Nat := 2124029672184769529313937

theorem tailTrace_4136533 : CollatzResearch.WordTrace tailWord_4136533 prefixEnd_4136533 2124029672184769529313937 := by
  unfold tailWord_4136533
  simp only [CollatzResearch.WordTrace]
  refine ⟨150871753123054879437070253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100581168748703252958046835 150871753123054879437070253)
  ·
    refine ⟨56576907421145579788901345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150871753123054879437070253 56576907421145579788901345)
    ·
      refine ⟨42432680565859184841676009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56576907421145579788901345 42432680565859184841676009)
      ·
        refine ⟨31824510424394388631257007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42432680565859184841676009 31824510424394388631257007)
        ·
          refine ⟨47736765636591582946885511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31824510424394388631257007 47736765636591582946885511)
          ·
            refine ⟨71605148454887374420328267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47736765636591582946885511 71605148454887374420328267)
            ·
              refine ⟨107407722682331061630492401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71605148454887374420328267 107407722682331061630492401)
              ·
                refine ⟨80555792011748296222869301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107407722682331061630492401 80555792011748296222869301)
                ·
                  refine ⟨7552105501101402770893997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80555792011748296222869301 7552105501101402770893997)
                  ·
                    refine ⟨2832039562913026039085249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7552105501101402770893997 2832039562913026039085249)
                    ·
                      refine ⟨2124029672184769529313937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832039562913026039085249 2124029672184769529313937)
                      ·
                        rfl

theorem cell23_4136533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_4136533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136533 prefixEnd_4136533 := by exact prefixLift 4136533
  have htrace : WordTrace (prefixWord ++ tailWord_4136533) baseStart_4136533 baseEnd_4136533 := by
    simpa [prefixWord, tailWord_4136533, baseEnd_4136533] using wordTrace_append hprefix tailTrace_4136533
  have hstable : (prefixWord ++ tailWord_4136533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136533).length < 2 ^ (prefixWord ++ tailWord_4136533).sum := by decide
  have hdescent : baseEnd_4136533 < baseStart_4136533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136540 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4136540 : Nat := 118140960795 + 4136540 * 2 ^ 59
def prefixEnd_4136540 : Nat := 4983230072969 + 3 ^ 40 * 4136540 * 2
def baseEnd_4136540 : Nat := 2124033266549351001926405

theorem tailTrace_4136540 : CollatzResearch.WordTrace tailWord_4136540 prefixEnd_4136540 2124033266549351001926405 := by
  unfold tailWord_4136540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75436004217014759816287537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100581338956019679755050049 75436004217014759816287537)
  ·
    refine ⟨56577003162761069862215653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75436004217014759816287537 56577003162761069862215653)
    ·
      refine ⟨10608188093017700599165435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56577003162761069862215653 10608188093017700599165435)
      ·
        refine ⟨15912282139526550898748153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608188093017700599165435 15912282139526550898748153)
        ·
          refine ⟨11934211604644913174061115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15912282139526550898748153 11934211604644913174061115)
          ·
            refine ⟨17901317406967369761091673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934211604644913174061115 17901317406967369761091673)
            ·
              refine ⟨13425988055225527320818755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17901317406967369761091673 13425988055225527320818755)
              ·
                refine ⟨20138982082838290981228133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425988055225527320818755 20138982082838290981228133)
                ·
                  refine ⟨3776059140532179558980275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20138982082838290981228133 3776059140532179558980275)
                  ·
                    refine ⟨5664088710798269338470413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776059140532179558980275 5664088710798269338470413)
                    ·
                      refine ⟨2124033266549351001926405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664088710798269338470413 2124033266549351001926405)
                      ·
                        rfl

theorem cell23_4136540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4136540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136540 prefixEnd_4136540 := by exact prefixLift 4136540
  have htrace : WordTrace (prefixWord ++ tailWord_4136540) baseStart_4136540 baseEnd_4136540 := by
    simpa [prefixWord, tailWord_4136540, baseEnd_4136540] using wordTrace_append hprefix tailTrace_4136540
  have hstable : (prefixWord ++ tailWord_4136540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136540).length < 2 ^ (prefixWord ++ tailWord_4136540).sum := by decide
  have hdescent : baseEnd_4136540 < baseStart_4136540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136541 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4136541 : Nat := 118140960795 + 4136541 * 2 ^ 59
def prefixEnd_4136541 : Nat := 4983230072969 + 3 ^ 40 * 4136541 * 2
def baseEnd_4136541 : Nat := 2124033780030005498013901

theorem tailTrace_4136541 : CollatzResearch.WordTrace tailWord_4136541 prefixEnd_4136541 2124033780030005498013901 := by
  unfold tailWord_4136541
  simp only [CollatzResearch.WordTrace]
  refine ⟨150872044907025896803361477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100581363271350597868907651 150872044907025896803361477)
  ·
    refine ⟨28288508420067355650630277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150872044907025896803361477 28288508420067355650630277)
    ·
      refine ⟨5304095328762629184493177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28288508420067355650630277 5304095328762629184493177)
      ·
        refine ⟨3978071496571971888369883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5304095328762629184493177 3978071496571971888369883)
        ·
          refine ⟨5967107244857957832554825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978071496571971888369883 5967107244857957832554825)
          ·
            refine ⟨4475330433643468374416119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5967107244857957832554825 4475330433643468374416119)
            ·
              refine ⟨6712995650465202561624179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475330433643468374416119 6712995650465202561624179)
              ·
                refine ⟨10069493475697803842436269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712995650465202561624179 10069493475697803842436269)
                ·
                  refine ⟨3776060053386676440913601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10069493475697803842436269 3776060053386676440913601)
                  ·
                    refine ⟨2832045040040007330685201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776060053386676440913601 2832045040040007330685201)
                    ·
                      refine ⟨2124033780030005498013901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832045040040007330685201 2124033780030005498013901)
                      ·
                        rfl

theorem cell23_4136541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4136541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136541 prefixEnd_4136541 := by exact prefixLift 4136541
  have htrace : WordTrace (prefixWord ++ tailWord_4136541) baseStart_4136541 baseEnd_4136541 := by
    simpa [prefixWord, tailWord_4136541, baseEnd_4136541] using wordTrace_append hprefix tailTrace_4136541
  have hstable : (prefixWord ++ tailWord_4136541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136541).length < 2 ^ (prefixWord ++ tailWord_4136541).sum := by decide
  have hdescent : baseEnd_4136541 < baseStart_4136541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136557 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4136557 : Nat := 118140960795 + 4136557 * 2 ^ 59
def prefixEnd_4136557 : Nat := 4983230072969 + 3 ^ 40 * 4136557 * 2
def baseEnd_4136557 : Nat := 2124041995720477435413827

theorem tailTrace_4136557 : CollatzResearch.WordTrace tailWord_4136557 prefixEnd_4136557 2124041995720477435413827 := by
  unfold tailWord_4136557
  simp only [CollatzResearch.WordTrace]
  refine ⟨150872628474967931535943925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100581752316645287690629283 150872628474967931535943925)
  ·
    refine ⟨14144308919528243581494743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150872628474967931535943925 14144308919528243581494743)
    ·
      refine ⟨21216463379292365372242115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14144308919528243581494743 21216463379292365372242115)
      ·
        refine ⟨31824695068938548058363173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216463379292365372242115 31824695068938548058363173)
        ·
          refine ⟨5967130325425977760943095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31824695068938548058363173 5967130325425977760943095)
          ·
            refine ⟨8950695488138966641414643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967130325425977760943095 8950695488138966641414643)
            ·
              refine ⟨13426043232208449962121965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950695488138966641414643 13426043232208449962121965)
              ·
                refine ⟨5034766212078168735795737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13426043232208449962121965 5034766212078168735795737)
                ·
                  refine ⟨3776074659058626551846803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5034766212078168735795737 3776074659058626551846803)
                  ·
                    refine ⟨5664111988587939827770205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776074659058626551846803 5664111988587939827770205)
                    ·
                      refine ⟨2124041995720477435413827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664111988587939827770205 2124041995720477435413827)
                      ·
                        rfl

theorem cell23_4136557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4136557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136557 prefixEnd_4136557 := by exact prefixLift 4136557
  have htrace : WordTrace (prefixWord ++ tailWord_4136557) baseStart_4136557 baseEnd_4136557 := by
    simpa [prefixWord, tailWord_4136557, baseEnd_4136557] using wordTrace_append hprefix tailTrace_4136557
  have hstable : (prefixWord ++ tailWord_4136557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136557).length < 2 ^ (prefixWord ++ tailWord_4136557).sum := by decide
  have hdescent : baseEnd_4136557 < baseStart_4136557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136623 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 5, 2]
def baseStart_4136623 : Nat := 118140960795 + 4136623 * 2 ^ 59
def prefixEnd_4136623 : Nat := 4983230072969 + 3 ^ 40 * 4136623 * 2
def baseEnd_4136623 : Nat := 2124075885443674177188523

theorem tailTrace_4136623 : CollatzResearch.WordTrace tailWord_4136623 prefixEnd_4136623 2124075885443674177188523 := by
  unfold tailWord_4136623
  simp only [CollatzResearch.WordTrace]
  refine ⟨150875035692728824807846523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100583357128485883205231015 150875035692728824807846523)
  ·
    refine ⟨226312553539093237211769785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150875035692728824807846523 226312553539093237211769785)
    ·
      refine ⟨169734415154319927908827339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226312553539093237211769785 169734415154319927908827339)
      ·
        refine ⟨254601622731479891863241009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169734415154319927908827339 254601622731479891863241009)
        ·
          refine ⟨190951217048609918897430757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254601622731479891863241009 190951217048609918897430757)
          ·
            refine ⟨35803353196614359793268267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190951217048609918897430757 35803353196614359793268267)
            ·
              refine ⟨53705029794921539689902401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35803353196614359793268267 53705029794921539689902401)
              ·
                refine ⟨40278772346191154767426801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53705029794921539689902401 40278772346191154767426801)
                ·
                  refine ⟨30209079259643366075570101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40278772346191154767426801 30209079259643366075570101)
                  ·
                    refine ⟨2832101180591565569584697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30209079259643366075570101 2832101180591565569584697)
                    ·
                      refine ⟨2124075885443674177188523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832101180591565569584697 2124075885443674177188523)
                      ·
                        rfl

theorem cell23_4136623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5, 2].length) (baseStart_4136623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136623 prefixEnd_4136623 := by exact prefixLift 4136623
  have htrace : WordTrace (prefixWord ++ tailWord_4136623) baseStart_4136623 baseEnd_4136623 := by
    simpa [prefixWord, tailWord_4136623, baseEnd_4136623] using wordTrace_append hprefix tailTrace_4136623
  have hstable : (prefixWord ++ tailWord_4136623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136623).length < 2 ^ (prefixWord ++ tailWord_4136623).sum := by decide
  have hdescent : baseEnd_4136623 < baseStart_4136623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136626 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_4136626 : Nat := 118140960795 + 4136626 * 2 ^ 59
def prefixEnd_4136626 : Nat := 4983230072969 + 3 ^ 40 * 4136626 * 2
def baseEnd_4136626 : Nat := 2124077425885637665451009

theorem tailTrace_4136626 : CollatzResearch.WordTrace tailWord_4136626 prefixEnd_4136626 2124077425885637665451009 := by
  unfold tailWord_4136626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37718786277929489080051433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100583430074478637546803821 37718786277929489080051433)
  ·
    refine ⟨28289089708447116810038575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37718786277929489080051433 28289089708447116810038575)
    ·
      refine ⟨42433634562670675215057863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28289089708447116810038575 42433634562670675215057863)
      ·
        refine ⟨63650451844006012822586795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42433634562670675215057863 63650451844006012822586795)
        ·
          refine ⟨95475677766009019233880193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63650451844006012822586795 95475677766009019233880193)
          ·
            refine ⟨71606758324506764425410145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95475677766009019233880193 71606758324506764425410145)
            ·
              refine ⟨53705068743380073319057609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71606758324506764425410145 53705068743380073319057609)
              ·
                refine ⟨40278801557535054989293207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53705068743380073319057609 40278801557535054989293207)
                ·
                  refine ⟨60418202336302582483939811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40278801557535054989293207 60418202336302582483939811)
                  ·
                    refine ⟨90627303504453873725909717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60418202336302582483939811 90627303504453873725909717)
                    ·
                      refine ⟨2124077425885637665451009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90627303504453873725909717 2124077425885637665451009)
                      ·
                        rfl

theorem cell23_4136626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_4136626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136626 prefixEnd_4136626 := by exact prefixLift 4136626
  have htrace : WordTrace (prefixWord ++ tailWord_4136626) baseStart_4136626 baseEnd_4136626 := by
    simpa [prefixWord, tailWord_4136626, baseEnd_4136626] using wordTrace_append hprefix tailTrace_4136626
  have hstable : (prefixWord ++ tailWord_4136626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136626).length < 2 ^ (prefixWord ++ tailWord_4136626).sum := by decide
  have hdescent : baseEnd_4136626 < baseStart_4136626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136633 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_4136633 : Nat := 118140960795 + 4136633 * 2 ^ 59
def prefixEnd_4136633 : Nat := 4983230072969 + 3 ^ 40 * 4136633 * 2
def baseEnd_4136633 : Nat := 708027006750073046021159

theorem tailTrace_4136633 : CollatzResearch.WordTrace tailWord_4136633 prefixEnd_4136633 708027006750073046021159 := by
  unfold tailWord_4136633
  simp only [CollatzResearch.WordTrace]
  refine ⟨150875400422692596515710553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100583600281795064343807035 150875400422692596515710553)
  ·
    refine ⟨113156550317019447386782915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150875400422692596515710553 113156550317019447386782915)
    ·
      refine ⟨169734825475529171080174373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113156550317019447386782915 169734825475529171080174373)
      ·
        refine ⟨31825279776661719577532695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169734825475529171080174373 31825279776661719577532695)
        ·
          refine ⟨47737919664992579366299043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31825279776661719577532695 47737919664992579366299043)
          ·
            refine ⟨71606879497488869049448565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47737919664992579366299043 71606879497488869049448565)
            ·
              refine ⟨6713144952889581473385803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71606879497488869049448565 6713144952889581473385803)
              ·
                refine ⟨10069717429334372210078705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6713144952889581473385803 10069717429334372210078705)
                ·
                  refine ⟨7552288072000779157559029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069717429334372210078705 7552288072000779157559029)
                  ·
                    refine ⟨708027006750073046021159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7552288072000779157559029 708027006750073046021159)
                    ·
                      rfl

theorem cell23_4136633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_4136633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136633 prefixEnd_4136633 := by exact prefixLift 4136633
  have htrace : WordTrace (prefixWord ++ tailWord_4136633) baseStart_4136633 baseEnd_4136633 := by
    simpa [prefixWord, tailWord_4136633, baseEnd_4136633] using wordTrace_append hprefix tailTrace_4136633
  have hstable : (prefixWord ++ tailWord_4136633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136633).length < 2 ^ (prefixWord ++ tailWord_4136633).sum := by decide
  have hdescent : baseEnd_4136633 < baseStart_4136633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136680 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_4136680 : Nat := 118140960795 + 4136680 * 2 ^ 59
def prefixEnd_4136680 : Nat := 4983230072969 + 3 ^ 40 * 4136680 * 2
def baseEnd_4136680 : Nat := 708035051280326818058587

theorem tailTrace_4136680 : CollatzResearch.WordTrace tailWord_4136680 prefixEnd_4136680 708035051280326818058587 := by
  unfold tailWord_4136680
  simp only [CollatzResearch.WordTrace]
  refine ⟨75438557326761161771335747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100584743102348215695114329 75438557326761161771335747)
  ·
    refine ⟨113157835990141742657003621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75438557326761161771335747 113157835990141742657003621)
    ·
      refine ⟨21217094248151576748188179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113157835990141742657003621 21217094248151576748188179)
      ·
        refine ⟨31825641372227365122282269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21217094248151576748188179 31825641372227365122282269)
        ·
          refine ⟨11934615514585261920855851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31825641372227365122282269 11934615514585261920855851)
          ·
            refine ⟨17901923271877892881283777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934615514585261920855851 17901923271877892881283777)
            ·
              refine ⟨13426442453908419660962833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17901923271877892881283777 13426442453908419660962833)
              ·
                refine ⟨10069831840431314745722125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13426442453908419660962833 10069831840431314745722125)
                ·
                  refine ⟨3776186940161743029645797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10069831840431314745722125 3776186940161743029645797)
                  ·
                    refine ⟨708035051280326818058587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3776186940161743029645797 708035051280326818058587)
                    ·
                      rfl

theorem cell23_4136680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_4136680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136680 prefixEnd_4136680 := by exact prefixLift 4136680
  have htrace : WordTrace (prefixWord ++ tailWord_4136680) baseStart_4136680 baseEnd_4136680 := by
    simpa [prefixWord, tailWord_4136680, baseEnd_4136680] using wordTrace_append hprefix tailTrace_4136680
  have hstable : (prefixWord ++ tailWord_4136680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136680).length < 2 ^ (prefixWord ++ tailWord_4136680).sum := by decide
  have hdescent : baseEnd_4136680 < baseStart_4136680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136690 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4136690 : Nat := 118140960795 + 4136690 * 2 ^ 59
def prefixEnd_4136690 : Nat := 4983230072969 + 3 ^ 40 * 4136690 * 2
def baseEnd_4136690 : Nat := 2124110288647525415050715

theorem tailTrace_4136690 : CollatzResearch.WordTrace tailWord_4136690 prefixEnd_4136690 2124110288647525415050715 := by
  unfold tailWord_4136690
  simp only [CollatzResearch.WordTrace]
  refine ⟨37719369845871523812633881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100584986255657396833690349 37719369845871523812633881)
  ·
    refine ⟨28289527384403642859475411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37719369845871523812633881 28289527384403642859475411)
    ·
      refine ⟨42434291076605464289213117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28289527384403642859475411 42434291076605464289213117)
      ·
        refine ⟨15912859153727049108454919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42434291076605464289213117 15912859153727049108454919)
        ·
          refine ⟨23869288730590573662682379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912859153727049108454919 23869288730590573662682379)
          ·
            refine ⟨35803933095885860494023569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23869288730590573662682379 35803933095885860494023569)
            ·
              refine ⟨26852949821914395370517677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35803933095885860494023569 26852949821914395370517677)
              ·
                refine ⟨10069856183217898263944129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26852949821914395370517677 10069856183217898263944129)
                ·
                  refine ⟨7552392137413423697958097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069856183217898263944129 7552392137413423697958097)
                  ·
                    refine ⟨5664294103060067773468573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7552392137413423697958097 5664294103060067773468573)
                    ·
                      refine ⟨2124110288647525415050715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664294103060067773468573 2124110288647525415050715)
                      ·
                        rfl

theorem cell23_4136690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4136690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136690 prefixEnd_4136690 := by exact prefixLift 4136690
  have htrace : WordTrace (prefixWord ++ tailWord_4136690) baseStart_4136690 baseEnd_4136690 := by
    simpa [prefixWord, tailWord_4136690, baseEnd_4136690] using wordTrace_append hprefix tailTrace_4136690
  have hstable : (prefixWord ++ tailWord_4136690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136690).length < 2 ^ (prefixWord ++ tailWord_4136690).sum := by decide
  have hdescent : baseEnd_4136690 < baseStart_4136690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136696 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_4136696 : Nat := 118140960795 + 4136696 * 2 ^ 59
def prefixEnd_4136696 : Nat := 4983230072969 + 3 ^ 40 * 4136696 * 2
def baseEnd_4136696 : Nat := 2124113369531452391575687

theorem tailTrace_4136696 : CollatzResearch.WordTrace tailWord_4136696 prefixEnd_4136696 2124113369531452391575687 := by
  unfold tailWord_4136696
  simp only [CollatzResearch.WordTrace]
  refine ⟨75438849110732179137626971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100585132147642905516835961 75438849110732179137626971)
  ·
    refine ⟨113158273666098268706440457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75438849110732179137626971 113158273666098268706440457)
    ·
      refine ⟨84868705249573701529830343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113158273666098268706440457 84868705249573701529830343)
      ·
        refine ⟨127303057874360552294745515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84868705249573701529830343 127303057874360552294745515)
        ·
          refine ⟨190954586811540828442118273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127303057874360552294745515 190954586811540828442118273)
          ·
            refine ⟨143215940108655621331588705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190954586811540828442118273 143215940108655621331588705)
            ·
              refine ⟨107411955081491715998691529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143215940108655621331588705 107411955081491715998691529)
              ·
                refine ⟨80558966311118786999018647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107411955081491715998691529 80558966311118786999018647)
                ·
                  refine ⟨120838449466678180498527971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80558966311118786999018647 120838449466678180498527971)
                  ·
                    refine ⟨181257674200017270747791957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120838449466678180498527971 181257674200017270747791957)
                    ·
                      refine ⟨2124113369531452391575687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 181257674200017270747791957 2124113369531452391575687)
                      ·
                        rfl

theorem cell23_4136696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_4136696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136696 prefixEnd_4136696 := by exact prefixLift 4136696
  have htrace : WordTrace (prefixWord ++ tailWord_4136696) baseStart_4136696 baseEnd_4136696 := by
    simpa [prefixWord, tailWord_4136696, baseEnd_4136696] using wordTrace_append hprefix tailTrace_4136696
  have hstable : (prefixWord ++ tailWord_4136696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136696).length < 2 ^ (prefixWord ++ tailWord_4136696).sum := by decide
  have hdescent : baseEnd_4136696 < baseStart_4136696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136714 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_4136714 : Nat := 118140960795 + 4136714 * 2 ^ 59
def prefixEnd_4136714 : Nat := 4983230072969 + 3 ^ 40 * 4136714 * 2
def baseEnd_4136714 : Nat := 708040870727744440383535

theorem tailTrace_4136714 : CollatzResearch.WordTrace tailWord_4136714 prefixEnd_4136714 708040870727744440383535 := by
  unfold tailWord_4136714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37719588683849786837352299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100585569823599431566272797 37719588683849786837352299)
  ·
    refine ⟨56579383025774680256028449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37719588683849786837352299 56579383025774680256028449)
    ·
      refine ⟨42434537269331010192021337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56579383025774680256028449 42434537269331010192021337)
      ·
        refine ⟨31825902951998257644016003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42434537269331010192021337 31825902951998257644016003)
        ·
          refine ⟨47738854427997386466024005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31825902951998257644016003 47738854427997386466024005)
          ·
            refine ⟨8951035205249509962379501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47738854427997386466024005 8951035205249509962379501)
            ·
              refine ⟨3356638201968566235892313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8951035205249509962379501 3356638201968566235892313)
              ·
                refine ⟨2517478651476424676919235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356638201968566235892313 2517478651476424676919235)
                ·
                  refine ⟨3776217977214637015378853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517478651476424676919235 3776217977214637015378853)
                  ·
                    refine ⟨708040870727744440383535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3776217977214637015378853 708040870727744440383535)
                    ·
                      rfl

theorem cell23_4136714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_4136714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136714 prefixEnd_4136714 := by exact prefixLift 4136714
  have htrace : WordTrace (prefixWord ++ tailWord_4136714) baseStart_4136714 baseEnd_4136714 := by
    simpa [prefixWord, tailWord_4136714, baseEnd_4136714] using wordTrace_append hprefix tailTrace_4136714
  have hstable : (prefixWord ++ tailWord_4136714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136714).length < 2 ^ (prefixWord ++ tailWord_4136714).sum := by decide
  have hdescent : baseEnd_4136714 < baseStart_4136714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136727 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 6]
def baseStart_4136727 : Nat := 118140960795 + 4136727 * 2 ^ 59
def prefixEnd_4136727 : Nat := 4983230072969 + 3 ^ 40 * 4136727 * 2
def baseEnd_4136727 : Nat := 236014365270193530032005

theorem tailTrace_4136727 : CollatzResearch.WordTrace tailWord_4136727 prefixEnd_4136727 236014365270193530032005 := by
  unfold tailWord_4136727
  simp only [CollatzResearch.WordTrace]
  refine ⟨150878828884352050569632435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100585885922901367046421623 150878828884352050569632435)
  ·
    refine ⟨226318243326528075854448653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150878828884352050569632435 226318243326528075854448653)
    ·
      refine ⟨84869341247448028445418245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226318243326528075854448653 84869341247448028445418245)
      ·
        refine ⟨15913001483896505333515921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84869341247448028445418245 15913001483896505333515921)
        ·
          refine ⟨11934751112922379000136941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15913001483896505333515921 11934751112922379000136941)
          ·
            refine ⟨4475531667345892125051353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11934751112922379000136941 4475531667345892125051353)
            ·
              refine ⟨3356648750509419093788515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4475531667345892125051353 3356648750509419093788515)
              ·
                refine ⟨5034973125764128640682773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356648750509419093788515 5034973125764128640682773)
                ·
                  refine ⟨236014365270193530032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5034973125764128640682773 236014365270193530032005)
                  ·
                    rfl

theorem cell23_4136727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 6].length) (baseStart_4136727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136727 prefixEnd_4136727 := by exact prefixLift 4136727
  have htrace : WordTrace (prefixWord ++ tailWord_4136727) baseStart_4136727 baseEnd_4136727 := by
    simpa [prefixWord, tailWord_4136727, baseEnd_4136727] using wordTrace_append hprefix tailTrace_4136727
  have hstable : (prefixWord ++ tailWord_4136727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136727).length < 2 ^ (prefixWord ++ tailWord_4136727).sum := by decide
  have hdescent : baseEnd_4136727 < baseStart_4136727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136740 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_4136740 : Nat := 118140960795 + 4136740 * 2 ^ 59
def prefixEnd_4136740 : Nat := 4983230072969 + 3 ^ 40 * 4136740 * 2
def baseEnd_4136740 : Nat := 708045320893416739808495

theorem tailTrace_4136740 : CollatzResearch.WordTrace tailWord_4136740 prefixEnd_4136740 708045320893416739808495 := by
  unfold tailWord_4136740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75439651516652476894927837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100586202022203302526570449 75439651516652476894927837)
  ·
    refine ⟨28289869318744678835597939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75439651516652476894927837 28289869318744678835597939)
    ·
      refine ⟨42434803978117018253396909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28289869318744678835597939 42434803978117018253396909)
      ·
        refine ⟨15913051491793881845023841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42434803978117018253396909 15913051491793881845023841)
        ·
          refine ⟨11934788618845411383767881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15913051491793881845023841 11934788618845411383767881)
          ·
            refine ⟨8951091464134058537825911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11934788618845411383767881 8951091464134058537825911)
            ·
              refine ⟨13426637196201087806738867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951091464134058537825911 13426637196201087806738867)
              ·
                refine ⟨20139955794301631710108301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13426637196201087806738867 20139955794301631710108301)
                ·
                  refine ⟨7552483422863111891290613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20139955794301631710108301 7552483422863111891290613)
                  ·
                    refine ⟨708045320893416739808495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7552483422863111891290613 708045320893416739808495)
                    ·
                      rfl

theorem cell23_4136740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_4136740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136740 prefixEnd_4136740 := by exact prefixLift 4136740
  have htrace : WordTrace (prefixWord ++ tailWord_4136740) baseStart_4136740 baseEnd_4136740 := by
    simpa [prefixWord, tailWord_4136740, baseEnd_4136740] using wordTrace_append hprefix tailTrace_4136740
  have hstable : (prefixWord ++ tailWord_4136740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136740).length < 2 ^ (prefixWord ++ tailWord_4136740).sum := by decide
  have hdescent : baseEnd_4136740 < baseStart_4136740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136753 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_4136753 : Nat := 118140960795 + 4136753 * 2 ^ 59
def prefixEnd_4136753 : Nat := 4983230072969 + 3 ^ 40 * 4136753 * 2
def baseEnd_4136753 : Nat := 708047545976252889520975

theorem tailTrace_4136753 : CollatzResearch.WordTrace tailWord_4136753 prefixEnd_4136753 708047545976252889520975 := by
  unfold tailWord_4136753
  simp only [CollatzResearch.WordTrace]
  refine ⟨150879777182257857010078913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100586518121505238006719275 150879777182257857010078913)
  ·
    refine ⟨113159832886693392757559185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150879777182257857010078913 113159832886693392757559185)
    ·
      refine ⟨84869874665020044568169389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113159832886693392757559185 84869874665020044568169389)
      ·
        refine ⟨31826202999382516713063521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84869874665020044568169389 31826202999382516713063521)
        ·
          refine ⟨23869652249536887534797641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31826202999382516713063521 23869652249536887534797641)
          ·
            refine ⟨17902239187152665651098231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23869652249536887534797641 17902239187152665651098231)
            ·
              refine ⟨26853358780728998476647347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902239187152665651098231 26853358780728998476647347)
              ·
                refine ⟨40280038171093497714971021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26853358780728998476647347 40280038171093497714971021)
                ·
                  refine ⟨15105014314160061643114133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40280038171093497714971021 15105014314160061643114133)
                  ·
                    refine ⟨708047545976252889520975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15105014314160061643114133 708047545976252889520975)
                    ·
                      rfl

theorem cell23_4136753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_4136753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136753 prefixEnd_4136753 := by exact prefixLift 4136753
  have htrace : WordTrace (prefixWord ++ tailWord_4136753) baseStart_4136753 baseEnd_4136753 := by
    simpa [prefixWord, tailWord_4136753, baseEnd_4136753] using wordTrace_append hprefix tailTrace_4136753
  have hstable : (prefixWord ++ tailWord_4136753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136753).length < 2 ^ (prefixWord ++ tailWord_4136753).sum := by decide
  have hdescent : baseEnd_4136753 < baseStart_4136753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136771 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 1, 1, 3]
def baseStart_4136771 : Nat := 118140960795 + 4136771 * 2 ^ 59
def prefixEnd_4136771 : Nat := 4983230072969 + 3 ^ 40 * 4136771 * 2
def baseEnd_4136771 : Nat := 2124151880580539598137843

theorem tailTrace_4136771 : CollatzResearch.WordTrace tailWord_4136771 prefixEnd_4136771 2124151880580539598137843 := by
  unfold tailWord_4136771
  simp only [CollatzResearch.WordTrace]
  refine ⟨150880433696192646084234167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100586955797461764056156111 150880433696192646084234167)
  ·
    refine ⟨226320650544288969126351251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150880433696192646084234167 226320650544288969126351251)
    ·
      refine ⟨339480975816433453689526877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226320650544288969126351251 339480975816433453689526877)
      ·
        refine ⟨127305365931162545133572579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339480975816433453689526877 127305365931162545133572579)
        ·
          refine ⟨190958048896743817700358869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127305365931162545133572579 190958048896743817700358869)
          ·
            refine ⟨4475579271017433227352161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 190958048896743817700358869 4475579271017433227352161)
            ·
              refine ⟨3356684453263074920514121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4475579271017433227352161 3356684453263074920514121)
              ·
                refine ⟨2517513339947306190385591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356684453263074920514121 2517513339947306190385591)
                ·
                  refine ⟨3776270009920959285578387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517513339947306190385591 3776270009920959285578387)
                  ·
                    refine ⟨5664405014881438928367581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776270009920959285578387 5664405014881438928367581)
                    ·
                      refine ⟨2124151880580539598137843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664405014881438928367581 2124151880580539598137843)
                      ·
                        rfl

theorem cell23_4136771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_4136771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136771 prefixEnd_4136771 := by exact prefixLift 4136771
  have htrace : WordTrace (prefixWord ++ tailWord_4136771) baseStart_4136771 baseEnd_4136771 := by
    simpa [prefixWord, tailWord_4136771, baseEnd_4136771] using wordTrace_append hprefix tailTrace_4136771
  have hstable : (prefixWord ++ tailWord_4136771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136771).length < 2 ^ (prefixWord ++ tailWord_4136771).sum := by decide
  have hdescent : baseEnd_4136771 < baseStart_4136771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136773 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_4136773 : Nat := 118140960795 + 4136773 * 2 ^ 59
def prefixEnd_4136773 : Nat := 4983230072969 + 3 ^ 40 * 4136773 * 2
def baseEnd_4136773 : Nat := 2124152907541848590312833

theorem tailTrace_4136773 : CollatzResearch.WordTrace tailWord_4136773 prefixEnd_4136773 2124152907541848590312833 := by
  unfold tailWord_4136773
  simp only [CollatzResearch.WordTrace]
  refine ⟨150880506642185400425806973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100587004428123600283871315 150880506642185400425806973)
  ·
    refine ⟨56580189990819525159677615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150880506642185400425806973 56580189990819525159677615)
    ·
      refine ⟨84870284986229287739516423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56580189990819525159677615 84870284986229287739516423)
      ·
        refine ⟨127305427479343931609274635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84870284986229287739516423 127305427479343931609274635)
        ·
          refine ⟨190958141219015897413911953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127305427479343931609274635 190958141219015897413911953)
          ·
            refine ⟨143218605914261923060433965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190958141219015897413911953 143218605914261923060433965)
            ·
              refine ⟨53706977217848221147662737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143218605914261923060433965 53706977217848221147662737)
              ·
                refine ⟨40280232913386165860747053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53706977217848221147662737 40280232913386165860747053)
                ·
                  refine ⟨15105087342519812197780145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40280232913386165860747053 15105087342519812197780145)
                  ·
                    refine ⟨11328815506889859148335109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15105087342519812197780145 11328815506889859148335109)
                    ·
                      refine ⟨2124152907541848590312833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11328815506889859148335109 2124152907541848590312833)
                      ·
                        rfl

theorem cell23_4136773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_4136773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136773 prefixEnd_4136773 := by exact prefixLift 4136773
  have htrace : WordTrace (prefixWord ++ tailWord_4136773) baseStart_4136773 baseEnd_4136773 := by
    simpa [prefixWord, tailWord_4136773, baseEnd_4136773] using wordTrace_append hprefix tailTrace_4136773
  have hstable : (prefixWord ++ tailWord_4136773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136773).length < 2 ^ (prefixWord ++ tailWord_4136773).sum := by decide
  have hdescent : baseEnd_4136773 < baseStart_4136773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136777 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 3, 2, 2]
def baseStart_4136777 : Nat := 118140960795 + 4136777 * 2 ^ 59
def prefixEnd_4136777 : Nat := 4983230072969 + 3 ^ 40 * 4136777 * 2
def baseEnd_4136777 : Nat := 2124154961464466574662815

theorem tailTrace_4136777 : CollatzResearch.WordTrace tailWord_4136777 prefixEnd_4136777 2124154961464466574662815 := by
  unfold tailWord_4136777
  simp only [CollatzResearch.WordTrace]
  refine ⟨150880652534170909108952585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100587101689447272739301723 150880652534170909108952585)
  ·
    refine ⟨113160489400628181831714439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150880652534170909108952585 113160489400628181831714439)
    ·
      refine ⟨169740734100942272747571659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113160489400628181831714439 169740734100942272747571659)
      ·
        refine ⟨254611101151413409121357489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169740734100942272747571659 254611101151413409121357489)
        ·
          refine ⟨190958325863560056841018117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254611101151413409121357489 190958325863560056841018117)
          ·
            refine ⟨35804686099417510657690897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190958325863560056841018117 35804686099417510657690897)
            ·
              refine ⟨26853514574563132993268173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35804686099417510657690897 26853514574563132993268173)
              ·
                refine ⟨10070067965461174872475565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26853514574563132993268173 10070067965461174872475565)
                ·
                  refine ⟨3776275487047940577178337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10070067965461174872475565 3776275487047940577178337)
                  ·
                    refine ⟨2832206615285955432883753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776275487047940577178337 2832206615285955432883753)
                    ·
                      refine ⟨2124154961464466574662815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832206615285955432883753 2124154961464466574662815)
                      ·
                        rfl

theorem cell23_4136777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2, 2].length) (baseStart_4136777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136777 prefixEnd_4136777 := by exact prefixLift 4136777
  have htrace : WordTrace (prefixWord ++ tailWord_4136777) baseStart_4136777 baseEnd_4136777 := by
    simpa [prefixWord, tailWord_4136777, baseEnd_4136777] using wordTrace_append hprefix tailTrace_4136777
  have hstable : (prefixWord ++ tailWord_4136777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136777).length < 2 ^ (prefixWord ++ tailWord_4136777).sum := by decide
  have hdescent : baseEnd_4136777 < baseStart_4136777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136800 : List Nat := [2, 1, 1, 3, 3, 3, 3, 7]
def baseStart_4136800 : Nat := 118140960795 + 4136800 * 2 ^ 59
def prefixEnd_4136800 : Nat := 4983230072969 + 3 ^ 40 * 4136800 * 2
def baseEnd_4136800 : Nat := 78672843389611851284267

theorem tailTrace_4136800 : CollatzResearch.WordTrace tailWord_4136800 prefixEnd_4136800 78672843389611851284267 := by
  unfold tailWord_4136800
  simp only [CollatzResearch.WordTrace]
  refine ⟨75440745706543792018519927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100587660942058389358026569 75440745706543792018519927)
  ·
    refine ⟨113161118559815688027779891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75440745706543792018519927 113161118559815688027779891)
    ·
      refine ⟨169741677839723532041669837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113161118559815688027779891 169741677839723532041669837)
      ·
        refine ⟨63653129189896324515626189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169741677839723532041669837 63653129189896324515626189)
        ·
          refine ⟨23869923446211121693359821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63653129189896324515626189 23869923446211121693359821)
          ·
            refine ⟨8951221292329170635009933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23869923446211121693359821 8951221292329170635009933)
            ·
              refine ⟨3356707984623438988128725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8951221292329170635009933 3356707984623438988128725)
              ·
                refine ⟨78672843389611851284267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3356707984623438988128725 78672843389611851284267)
                ·
                  rfl

theorem cell23_4136800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 7].length) (baseStart_4136800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136800 prefixEnd_4136800 := by exact prefixLift 4136800
  have htrace : WordTrace (prefixWord ++ tailWord_4136800) baseStart_4136800 baseEnd_4136800 := by
    simpa [prefixWord, tailWord_4136800, baseEnd_4136800] using wordTrace_append hprefix tailTrace_4136800
  have hstable : (prefixWord ++ tailWord_4136800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136800).length < 2 ^ (prefixWord ++ tailWord_4136800).sum := by decide
  have hdescent : baseEnd_4136800 < baseStart_4136800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136814 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4136814 : Nat := 118140960795 + 4136814 * 2 ^ 59
def prefixEnd_4136814 : Nat := 4983230072969 + 3 ^ 40 * 4136814 * 2
def baseEnd_4136814 : Nat := 2124173960248682929900145

theorem tailTrace_4136814 : CollatzResearch.WordTrace tailWord_4136814 prefixEnd_4136814 2124173960248682929900145 := by
  unfold tailWord_4136814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860250254379608053506187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100588001356691242952032997 18860250254379608053506187)
  ·
    refine ⟨28290375381569412080259281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860250254379608053506187 28290375381569412080259281)
    ·
      refine ⟨21217781536177059060194461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28290375381569412080259281 21217781536177059060194461)
      ·
        refine ⟨7956668076066397147572923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21217781536177059060194461 7956668076066397147572923)
        ·
          refine ⟨11935002114099595721359385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956668076066397147572923 11935002114099595721359385)
          ·
            refine ⟨8951251585574696791019539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11935002114099595721359385 8951251585574696791019539)
            ·
              refine ⟨13426877378362045186529309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951251585574696791019539 13426877378362045186529309)
              ·
                refine ⟨5035079016885766944948491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13426877378362045186529309 5035079016885766944948491)
                ·
                  refine ⟨7552618525328650417422737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035079016885766944948491 7552618525328650417422737)
                  ·
                    refine ⟨5664463893996487813067053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7552618525328650417422737 5664463893996487813067053)
                    ·
                      refine ⟨2124173960248682929900145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664463893996487813067053 2124173960248682929900145)
                      ·
                        rfl

theorem cell23_4136814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4136814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136814 prefixEnd_4136814 := by exact prefixLift 4136814
  have htrace : WordTrace (prefixWord ++ tailWord_4136814) baseStart_4136814 baseEnd_4136814 := by
    simpa [prefixWord, tailWord_4136814, baseEnd_4136814] using wordTrace_append hprefix tailTrace_4136814
  have hstable : (prefixWord ++ tailWord_4136814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136814).length < 2 ^ (prefixWord ++ tailWord_4136814).sum := by decide
  have hdescent : baseEnd_4136814 < baseStart_4136814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136862 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4136862 : Nat := 118140960795 + 4136862 * 2 ^ 59
def prefixEnd_4136862 : Nat := 4983230072969 + 3 ^ 40 * 4136862 * 2
def baseEnd_4136862 : Nat := 2124198607320098742099925

theorem tailTrace_4136862 : CollatzResearch.WordTrace tailWord_4136862 prefixEnd_4136862 2124198607320098742099925 := by
  unfold tailWord_4136862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860469092357871078224605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100589168492575312417197893 18860469092357871078224605)
  ·
    refine ⟨7072675909634201654334227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18860469092357871078224605 7072675909634201654334227)
    ·
      refine ⟨10609013864451302481501341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7072675909634201654334227 10609013864451302481501341)
      ·
        refine ⟨3978380199169238430563003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10609013864451302481501341 3978380199169238430563003)
        ·
          refine ⟨5967570298753857645844505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978380199169238430563003 5967570298753857645844505)
          ·
            refine ⟨4475677724065393234383379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5967570298753857645844505 4475677724065393234383379)
            ·
              refine ⟨6713516586098089851575069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475677724065393234383379 6713516586098089851575069)
              ·
                refine ⟨2517568719786783694340651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6713516586098089851575069 2517568719786783694340651)
                ·
                  refine ⟨3776353079680175541510977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517568719786783694340651 3776353079680175541510977)
                  ·
                    refine ⟨2832264809760131656133233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776353079680175541510977 2832264809760131656133233)
                    ·
                      refine ⟨2124198607320098742099925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832264809760131656133233 2124198607320098742099925)
                      ·
                        rfl

theorem cell23_4136862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4136862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136862 prefixEnd_4136862 := by exact prefixLift 4136862
  have htrace : WordTrace (prefixWord ++ tailWord_4136862) baseStart_4136862 baseEnd_4136862 := by
    simpa [prefixWord, tailWord_4136862, baseEnd_4136862] using wordTrace_append hprefix tailTrace_4136862
  have hstable : (prefixWord ++ tailWord_4136862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136862).length < 2 ^ (prefixWord ++ tailWord_4136862).sum := by decide
  have hdescent : baseEnd_4136862 < baseStart_4136862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136883 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_4136883 : Nat := 118140960795 + 4136883 * 2 ^ 59
def prefixEnd_4136883 : Nat := 4983230072969 + 3 ^ 40 * 4136883 * 2
def baseEnd_4136883 : Nat := 2124209390413843159937327

theorem tailTrace_4136883 : CollatzResearch.WordTrace tailWord_4136883 prefixEnd_4136883 2124209390413843159937327 := by
  unfold tailWord_4136883
  simp only [CollatzResearch.WordTrace]
  refine ⟨150884518671786889212311303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100589679114524592808207535 150884518671786889212311303)
  ·
    refine ⟨226326778007680333818466955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150884518671786889212311303 226326778007680333818466955)
    ·
      refine ⟨339490167011520500727700433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226326778007680333818466955 339490167011520500727700433)
      ·
        refine ⟨254617625258640375545775325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339490167011520500727700433 254617625258640375545775325)
        ·
          refine ⟨95481609471990140829665747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254617625258640375545775325 95481609471990140829665747)
          ·
            refine ⟨143222414207985211244498621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95481609471990140829665747 143222414207985211244498621)
            ·
              refine ⟨53708405327994454216686983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143222414207985211244498621 53708405327994454216686983)
              ·
                refine ⟨80562607991991681325030475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53708405327994454216686983 80562607991991681325030475)
                ·
                  refine ⟨120843911987987521987545713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80562607991991681325030475 120843911987987521987545713)
                  ·
                    refine ⟨90632933990990641490659285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120843911987987521987545713 90632933990990641490659285)
                    ·
                      refine ⟨2124209390413843159937327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90632933990990641490659285 2124209390413843159937327)
                      ·
                        rfl

theorem cell23_4136883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_4136883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136883 prefixEnd_4136883 := by exact prefixLift 4136883
  have htrace : WordTrace (prefixWord ++ tailWord_4136883) baseStart_4136883 baseEnd_4136883 := by
    simpa [prefixWord, tailWord_4136883, baseEnd_4136883] using wordTrace_append hprefix tailTrace_4136883
  have hstable : (prefixWord ++ tailWord_4136883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136883).length < 2 ^ (prefixWord ++ tailWord_4136883).sum := by decide
  have hdescent : baseEnd_4136883 < baseStart_4136883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136941 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 5]
def baseStart_4136941 : Nat := 118140960795 + 4136941 * 2 ^ 59
def prefixEnd_4136941 : Nat := 4983230072969 + 3 ^ 40 * 4136941 * 2
def baseEnd_4136941 : Nat := 236026574699089325890229

theorem tailTrace_4136941 : CollatzResearch.WordTrace tailWord_4136941 prefixEnd_4136941 236026574699089325890229 := by
  unfold tailWord_4136941
  simp only [CollatzResearch.WordTrace]
  refine ⟨150886634105576765117922677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100591089403717843411948451 150886634105576765117922677)
  ·
    refine ⟨14145621947397821729805251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150886634105576765117922677 14145621947397821729805251)
    ·
      refine ⟨21218432921096732594707877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14145621947397821729805251 21218432921096732594707877)
      ·
        refine ⟨3978456172705637361507727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21218432921096732594707877 3978456172705637361507727)
        ·
          refine ⟨5967684259058456042261591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978456172705637361507727 5967684259058456042261591)
          ·
            refine ⟨8951526388587684063392387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967684259058456042261591 8951526388587684063392387)
            ·
              refine ⟨13427289582881526095088581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951526388587684063392387 13427289582881526095088581)
              ·
                refine ⟨2517616796790286142829109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13427289582881526095088581 2517616796790286142829109)
                ·
                  refine ⟨236026574699089325890229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2517616796790286142829109 236026574699089325890229)
                  ·
                    rfl

theorem cell23_4136941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_4136941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136941 prefixEnd_4136941 := by exact prefixLift 4136941
  have htrace : WordTrace (prefixWord ++ tailWord_4136941) baseStart_4136941 baseEnd_4136941 := by
    simpa [prefixWord, tailWord_4136941, baseEnd_4136941] using wordTrace_append hprefix tailTrace_4136941
  have hstable : (prefixWord ++ tailWord_4136941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136941).length < 2 ^ (prefixWord ++ tailWord_4136941).sum := by decide
  have hdescent : baseEnd_4136941 < baseStart_4136941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136957 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_4136957 : Nat := 118140960795 + 4136957 * 2 ^ 59
def prefixEnd_4136957 : Nat := 4983230072969 + 3 ^ 40 * 4136957 * 2
def baseEnd_4136957 : Nat := 2124247387982275870411987

theorem tailTrace_4136957 : CollatzResearch.WordTrace tailWord_4136957 prefixEnd_4136957 2124247387982275870411987 := by
  unfold tailWord_4136957
  simp only [CollatzResearch.WordTrace]
  refine ⟨150887217673518799850505125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100591478449012533233670083 150887217673518799850505125)
  ·
    refine ⟨28291353313784774971969711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150887217673518799850505125 28291353313784774971969711)
    ·
      refine ⟨42437029970677162457954567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28291353313784774971969711 42437029970677162457954567)
      ·
        refine ⟨63655544956015743686931851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42437029970677162457954567 63655544956015743686931851)
        ·
          refine ⟨95483317434023615530397777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63655544956015743686931851 95483317434023615530397777)
          ·
            refine ⟨71612488075517711647798333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95483317434023615530397777 71612488075517711647798333)
            ·
              refine ⟨26854683028319141867924375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71612488075517711647798333 26854683028319141867924375)
              ·
                refine ⟨40282024542478712801886563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26854683028319141867924375 40282024542478712801886563)
                ·
                  refine ⟨60423036813718069202829845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40282024542478712801886563 60423036813718069202829845)
                  ·
                    refine ⟨2832329850643034493882649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60423036813718069202829845 2832329850643034493882649)
                    ·
                      refine ⟨2124247387982275870411987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832329850643034493882649 2124247387982275870411987)
                      ·
                        rfl

theorem cell23_4136957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_4136957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136957 prefixEnd_4136957 := by exact prefixLift 4136957
  have htrace : WordTrace (prefixWord ++ tailWord_4136957) baseStart_4136957 baseEnd_4136957 := by
    simpa [prefixWord, tailWord_4136957, baseEnd_4136957] using wordTrace_append hprefix tailTrace_4136957
  have hstable : (prefixWord ++ tailWord_4136957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136957).length < 2 ^ (prefixWord ++ tailWord_4136957).sum := by decide
  have hdescent : baseEnd_4136957 < baseStart_4136957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136967 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 5, 4]
def baseStart_4136967 : Nat := 118140960795 + 4136967 * 2 ^ 59
def prefixEnd_4136967 : Nat := 4983230072969 + 3 ^ 40 * 4136967 * 2
def baseEnd_4136967 : Nat := 708084174262940277095647

theorem tailTrace_4136967 : CollatzResearch.WordTrace tailWord_4136967 prefixEnd_4136967 708084174262940277095647 := by
  unfold tailWord_4136967
  simp only [CollatzResearch.WordTrace]
  refine ⟨150887582403482571558369155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100591721602321714372246103 150887582403482571558369155)
  ·
    refine ⟨226331373605223857337553733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150887582403482571558369155 226331373605223857337553733)
    ·
      refine ⟨42437132550979473250791325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226331373605223857337553733 42437132550979473250791325)
      ·
        refine ⟨15913924706617302469046747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42437132550979473250791325 15913924706617302469046747)
        ·
          refine ⟨23870887059925953703570121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15913924706617302469046747 23870887059925953703570121)
          ·
            refine ⟨17903165294944465277677591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23870887059925953703570121 17903165294944465277677591)
            ·
              refine ⟨26854747942416697916516387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903165294944465277677591 26854747942416697916516387)
              ·
                refine ⟨40282121913625046874774581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26854747942416697916516387 40282121913625046874774581)
                ·
                  refine ⟨3776448929402348144510117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40282121913625046874774581 3776448929402348144510117)
                  ·
                    refine ⟨708084174262940277095647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3776448929402348144510117 708084174262940277095647)
                    ·
                      rfl

theorem cell23_4136967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_4136967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136967 prefixEnd_4136967 := by exact prefixLift 4136967
  have htrace : WordTrace (prefixWord ++ tailWord_4136967) baseStart_4136967 baseEnd_4136967 := by
    simpa [prefixWord, tailWord_4136967, baseEnd_4136967] using wordTrace_append hprefix tailTrace_4136967
  have hstable : (prefixWord ++ tailWord_4136967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136967).length < 2 ^ (prefixWord ++ tailWord_4136967).sum := by decide
  have hdescent : baseEnd_4136967 < baseStart_4136967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136997 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 6]
def baseStart_4136997 : Nat := 118140960795 + 4136997 * 2 ^ 59
def prefixEnd_4136997 : Nat := 4983230072969 + 3 ^ 40 * 4136997 * 2
def baseEnd_4136997 : Nat := 236029769689828412656867

theorem tailTrace_4136997 : CollatzResearch.WordTrace tailWord_4136997 prefixEnd_4136997 236029769689828412656867 := by
  unfold tailWord_4136997
  simp only [CollatzResearch.WordTrace]
  refine ⟨150888676593373886681961245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100592451062249257787974163 150888676593373886681961245)
  ·
    refine ⟨56583253722515207505735467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150888676593373886681961245 56583253722515207505735467)
    ·
      refine ⟨84874880583772811258603201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56583253722515207505735467 84874880583772811258603201)
      ·
        refine ⟨63656160437829608443952401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84874880583772811258603201 63656160437829608443952401)
        ·
          refine ⟨47742120328372206332964301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63656160437829608443952401 47742120328372206332964301)
          ·
            refine ⟨17903295123139577374861613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47742120328372206332964301 17903295123139577374861613)
            ·
              refine ⟨6713735671177341515573105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17903295123139577374861613 6713735671177341515573105)
              ·
                refine ⟨5035301753383006136679829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6713735671177341515573105 5035301753383006136679829)
                ·
                  refine ⟨236029769689828412656867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5035301753383006136679829 236029769689828412656867)
                  ·
                    rfl

theorem cell23_4136997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_4136997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4136997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4136997 prefixEnd_4136997 := by exact prefixLift 4136997
  have htrace : WordTrace (prefixWord ++ tailWord_4136997) baseStart_4136997 baseEnd_4136997 := by
    simpa [prefixWord, tailWord_4136997, baseEnd_4136997] using wordTrace_append hprefix tailTrace_4136997
  have hstable : (prefixWord ++ tailWord_4136997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136997).length < 2 ^ (prefixWord ++ tailWord_4136997).sum := by decide
  have hdescent : baseEnd_4136997 < baseStart_4136997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137024 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3]
def baseStart_4137024 : Nat := 118140960795 + 4137024 * 2 ^ 59
def prefixEnd_4137024 : Nat := 4983230072969 + 3 ^ 40 * 4137024 * 2
def baseEnd_4137024 : Nat := 2124281791186127108274179

theorem tailTrace_4137024 : CollatzResearch.WordTrace tailWord_4137024 prefixEnd_4137024 2124281791186127108274179 := by
  unfold tailWord_4137024
  simp only [CollatzResearch.WordTrace]
  refine ⟨75444830682138035146597063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100593107576184046862129417 75444830682138035146597063)
  ·
    refine ⟨113167246023207052719895595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75444830682138035146597063 113167246023207052719895595)
    ·
      refine ⟨169750869034810579079843393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113167246023207052719895595 169750869034810579079843393)
      ·
        refine ⟨127313151776107934309882545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169750869034810579079843393 127313151776107934309882545)
        ·
          refine ⟨95484863832080950732411909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127313151776107934309882545 95484863832080950732411909)
          ·
            refine ⟨17903411968515178262327233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95484863832080950732411909 17903411968515178262327233)
            ·
              refine ⟨13427558976386383696745425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17903411968515178262327233 13427558976386383696745425)
              ·
                refine ⟨10070669232289787772559069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13427558976386383696745425 10070669232289787772559069)
                ·
                  refine ⟨3776500962108670414709651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10070669232289787772559069 3776500962108670414709651)
                  ·
                    refine ⟨5664751443163005622064477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776500962108670414709651 5664751443163005622064477)
                    ·
                      refine ⟨2124281791186127108274179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664751443163005622064477 2124281791186127108274179)
                      ·
                        rfl

theorem cell23_4137024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_4137024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137024 prefixEnd_4137024 := by exact prefixLift 4137024
  have htrace : WordTrace (prefixWord ++ tailWord_4137024) baseStart_4137024 baseEnd_4137024 := by
    simpa [prefixWord, tailWord_4137024, baseEnd_4137024] using wordTrace_append hprefix tailTrace_4137024
  have hstable : (prefixWord ++ tailWord_4137024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137024).length < 2 ^ (prefixWord ++ tailWord_4137024).sum := by decide
  have hdescent : baseEnd_4137024 < baseStart_4137024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137034 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_4137034 : Nat := 118140960795 + 4137034 * 2 ^ 59
def prefixEnd_4137034 : Nat := 4983230072969 + 3 ^ 40 * 4137034 * 2
def baseEnd_4137034 : Nat := 2124286925992672069149133

theorem tailTrace_4137034 : CollatzResearch.WordTrace tailWord_4137034 prefixEnd_4137034 2124286925992672069149133 := by
  unfold tailWord_4137034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37722506523559960500264539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100593350729493228000705437 37722506523559960500264539)
  ·
    refine ⟨56583759785339940750396809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37722506523559960500264539 56583759785339940750396809)
    ·
      refine ⟨42437819839004955562797607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56583759785339940750396809 42437819839004955562797607)
      ·
        refine ⟨63656729758507433344196411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42437819839004955562797607 63656729758507433344196411)
        ·
          refine ⟨95485094637761150016294617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63656729758507433344196411 95485094637761150016294617)
          ·
            refine ⟨71613820978320862512220963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95485094637761150016294617 71613820978320862512220963)
            ·
              refine ⟨107420731467481293768331445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71613820978320862512220963 107420731467481293768331445)
              ·
                refine ⟨10070693575076371290781073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107420731467481293768331445 10070693575076371290781073)
                ·
                  refine ⟨7553020181307278468085805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10070693575076371290781073 7553020181307278468085805)
                  ·
                    refine ⟨2832382567990229425532177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7553020181307278468085805 2832382567990229425532177)
                    ·
                      refine ⟨2124286925992672069149133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832382567990229425532177 2124286925992672069149133)
                      ·
                        rfl

theorem cell23_4137034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_4137034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137034 prefixEnd_4137034 := by exact prefixLift 4137034
  have htrace : WordTrace (prefixWord ++ tailWord_4137034) baseStart_4137034 baseEnd_4137034 := by
    simpa [prefixWord, tailWord_4137034, baseEnd_4137034] using wordTrace_append hprefix tailTrace_4137034
  have hstable : (prefixWord ++ tailWord_4137034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137034).length < 2 ^ (prefixWord ++ tailWord_4137034).sum := by decide
  have hdescent : baseEnd_4137034 < baseStart_4137034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137081 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_4137081 : Nat := 118140960795 + 4137081 * 2 ^ 59
def prefixEnd_4137081 : Nat := 4983230072969 + 3 ^ 40 * 4137081 * 2
def baseEnd_4137081 : Nat := 2124311059583433385261417

theorem tailTrace_4137081 : CollatzResearch.WordTrace tailWord_4137081 prefixEnd_4137081 2124311059583433385261417 := by
  unfold tailWord_4137081
  simp only [CollatzResearch.WordTrace]
  refine ⟨150891740325069569028019097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100594493550046379352012731 150891740325069569028019097)
  ·
    refine ⟨113168805243802176771014323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150891740325069569028019097 113168805243802176771014323)
    ·
      refine ⟨169753207865703265156521485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113168805243802176771014323 169753207865703265156521485)
      ·
        refine ⟨63657452949638724433695557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169753207865703265156521485 63657452949638724433695557)
        ·
          refine ⟨11935772428057260831317917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63657452949638724433695557 11935772428057260831317917)
          ·
            refine ⟨4475914660521472811744219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11935772428057260831317917 4475914660521472811744219)
            ·
              refine ⟨6713871990782209217616329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475914660521472811744219 6713871990782209217616329)
              ·
                refine ⟨5035403993086656913212247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6713871990782209217616329 5035403993086656913212247)
                ·
                  refine ⟨7553105989629985369818371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035403993086656913212247 7553105989629985369818371)
                  ·
                    refine ⟨11329658984444978054727557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553105989629985369818371 11329658984444978054727557)
                    ·
                      refine ⟨2124311059583433385261417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11329658984444978054727557 2124311059583433385261417)
                      ·
                        rfl

theorem cell23_4137081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_4137081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137081 prefixEnd_4137081 := by exact prefixLift 4137081
  have htrace : WordTrace (prefixWord ++ tailWord_4137081) baseStart_4137081 baseEnd_4137081 := by
    simpa [prefixWord, tailWord_4137081, baseEnd_4137081] using wordTrace_append hprefix tailTrace_4137081
  have hstable : (prefixWord ++ tailWord_4137081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137081).length < 2 ^ (prefixWord ++ tailWord_4137081).sum := by decide
  have hdescent : baseEnd_4137081 < baseStart_4137081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137084 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_4137084 : Nat := 118140960795 + 4137084 * 2 ^ 59
def prefixEnd_4137084 : Nat := 4983230072969 + 3 ^ 40 * 4137084 * 2
def baseEnd_4137084 : Nat := 2124312600025396873523903

theorem tailTrace_4137084 : CollatzResearch.WordTrace tailWord_4137084 prefixEnd_4137084 2124312600025396873523903 := by
  unfold tailWord_4137084
  simp only [CollatzResearch.WordTrace]
  refine ⟨75445924872029350270189153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100594566496039133693585537 75445924872029350270189153)
  ·
    refine ⟨56584443654022012702641865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75445924872029350270189153 56584443654022012702641865)
    ·
      refine ⟨42438332740516509526981399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56584443654022012702641865 42438332740516509526981399)
      ·
        refine ⟨63657499110774764290472099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42438332740516509526981399 63657499110774764290472099)
        ·
          refine ⟨95486248666162146435708149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63657499110774764290472099 95486248666162146435708149)
          ·
            refine ⟨8951835812452701228347639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95486248666162146435708149 8951835812452701228347639)
            ·
              refine ⟨13427753718679051842521459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951835812452701228347639 13427753718679051842521459)
              ·
                refine ⟨20141630578018577763782189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427753718679051842521459 20141630578018577763782189)
                ·
                  refine ⟨7553111466756966661418321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20141630578018577763782189 7553111466756966661418321)
                  ·
                    refine ⟨5664833600067724996063741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7553111466756966661418321 5664833600067724996063741)
                    ·
                      refine ⟨2124312600025396873523903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5664833600067724996063741 2124312600025396873523903)
                      ·
                        rfl

theorem cell23_4137084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_4137084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137084 prefixEnd_4137084 := by exact prefixLift 4137084
  have htrace : WordTrace (prefixWord ++ tailWord_4137084) baseStart_4137084 baseEnd_4137084 := by
    simpa [prefixWord, tailWord_4137084, baseEnd_4137084] using wordTrace_append hprefix tailTrace_4137084
  have hstable : (prefixWord ++ tailWord_4137084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137084).length < 2 ^ (prefixWord ++ tailWord_4137084).sum := by decide
  have hdescent : baseEnd_4137084 < baseStart_4137084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137117 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_4137117 : Nat := 118140960795 + 4137117 * 2 ^ 59
def prefixEnd_4137117 : Nat := 4983230072969 + 3 ^ 40 * 4137117 * 2
def baseEnd_4137117 : Nat := 708109848295665081470417

theorem tailTrace_4137117 : CollatzResearch.WordTrace tailWord_4137117 prefixEnd_4137117 708109848295665081470417 := by
  unfold tailWord_4137117
  simp only [CollatzResearch.WordTrace]
  refine ⟨150893053352939147176329605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100595368901959431450886403 150893053352939147176329605)
  ·
    refine ⟨28292447503676090095561801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150893053352939147176329605 28292447503676090095561801)
    ·
      refine ⟨21219335627757067571671351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28292447503676090095561801 21219335627757067571671351)
      ·
        refine ⟨31829003441635601357507027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21219335627757067571671351 31829003441635601357507027)
        ·
          refine ⟨47743505162453402036260541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31829003441635601357507027 47743505162453402036260541)
          ·
            refine ⟨17903814435920025763597703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47743505162453402036260541 17903814435920025763597703)
            ·
              refine ⟨26855721653880038645396555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903814435920025763597703 26855721653880038645396555)
              ·
                refine ⟨40283582480820057968094833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26855721653880038645396555 40283582480820057968094833)
                ·
                  refine ⟨30212686860615043476071125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40283582480820057968094833 30212686860615043476071125)
                  ·
                    refine ⟨708109848295665081470417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30212686860615043476071125 708109848295665081470417)
                    ·
                      rfl

theorem cell23_4137117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_4137117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137117 prefixEnd_4137117 := by exact prefixLift 4137117
  have htrace : WordTrace (prefixWord ++ tailWord_4137117) baseStart_4137117 baseEnd_4137117 := by
    simpa [prefixWord, tailWord_4137117, baseEnd_4137117] using wordTrace_append hprefix tailTrace_4137117
  have hstable : (prefixWord ++ tailWord_4137117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137117).length < 2 ^ (prefixWord ++ tailWord_4137117).sum := by decide
  have hdescent : baseEnd_4137117 < baseStart_4137117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137157 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_4137157 : Nat := 118140960795 + 4137157 * 2 ^ 59
def prefixEnd_4137157 : Nat := 4983230072969 + 3 ^ 40 * 4137157 * 2
def baseEnd_4137157 : Nat := 2124350084113175087911067

theorem tailTrace_4137157 : CollatzResearch.WordTrace tailWord_4137157 prefixEnd_4137157 2124350084113175087911067 := by
  unfold tailWord_4137157
  simp only [CollatzResearch.WordTrace]
  refine ⟨150894512272794234007785725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100596341515196156005190483 150894512272794234007785725)
  ·
    refine ⟨56585442102297837752919647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150894512272794234007785725 56585442102297837752919647)
    ·
      refine ⟨84878163153446756629379471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56585442102297837752919647 84878163153446756629379471)
      ·
        refine ⟨127317244730170134944069207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84878163153446756629379471 127317244730170134944069207)
        ·
          refine ⟨190975867095255202416103811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127317244730170134944069207 190975867095255202416103811)
          ·
            refine ⟨286463800642882803624155717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190975867095255202416103811 286463800642882803624155717)
            ·
              refine ⟨53711962620540525679529197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286463800642882803624155717 53711962620540525679529197)
              ·
                refine ⟨20141985982702697129823449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53711962620540525679529197 20141985982702697129823449)
                ·
                  refine ⟨15106489487027022847367587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20141985982702697129823449 15106489487027022847367587)
                  ·
                    refine ⟨22659734230540534271051381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15106489487027022847367587 22659734230540534271051381)
                    ·
                      refine ⟨2124350084113175087911067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22659734230540534271051381 2124350084113175087911067)
                      ·
                        rfl

theorem cell23_4137157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_4137157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137157 prefixEnd_4137157 := by exact prefixLift 4137157
  have htrace : WordTrace (prefixWord ++ tailWord_4137157) baseStart_4137157 baseEnd_4137157 := by
    simpa [prefixWord, tailWord_4137157, baseEnd_4137157] using wordTrace_append hprefix tailTrace_4137157
  have hstable : (prefixWord ++ tailWord_4137157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137157).length < 2 ^ (prefixWord ++ tailWord_4137157).sum := by decide
  have hdescent : baseEnd_4137157 < baseStart_4137157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137167 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_4137167 : Nat := 118140960795 + 4137167 * 2 ^ 59
def prefixEnd_4137167 : Nat := 4983230072969 + 3 ^ 40 * 4137167 * 2
def baseEnd_4137167 : Nat := 2124355218919720048786021

theorem tailTrace_4137167 : CollatzResearch.WordTrace tailWord_4137167 prefixEnd_4137167 2124355218919720048786021 := by
  unfold tailWord_4137167
  simp only [CollatzResearch.WordTrace]
  refine ⟨150894877002758005715649755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100596584668505337143766503 150894877002758005715649755)
  ·
    refine ⟨226342315504137008573474633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150894877002758005715649755 226342315504137008573474633)
    ·
      refine ⟨169756736628102756430105975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226342315504137008573474633 169756736628102756430105975)
      ·
        refine ⟨254635104942154134645158963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169756736628102756430105975 254635104942154134645158963)
        ·
          refine ⟨381952657413231201967738445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254635104942154134645158963 381952657413231201967738445)
          ·
            refine ⟨143232246529961700737901917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381952657413231201967738445 143232246529961700737901917)
            ·
              refine ⟨53712092448735637776713219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143232246529961700737901917 53712092448735637776713219)
              ·
                refine ⟨80568138673103456665069829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53712092448735637776713219 80568138673103456665069829)
                ·
                  refine ⟨15106526001206898124700593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80568138673103456665069829 15106526001206898124700593)
                  ·
                    refine ⟨11329894500905173593525445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15106526001206898124700593 11329894500905173593525445)
                    ·
                      refine ⟨2124355218919720048786021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11329894500905173593525445 2124355218919720048786021)
                      ·
                        rfl

theorem cell23_4137167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_4137167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137167 prefixEnd_4137167 := by exact prefixLift 4137167
  have htrace : WordTrace (prefixWord ++ tailWord_4137167) baseStart_4137167 baseEnd_4137167 := by
    simpa [prefixWord, tailWord_4137167, baseEnd_4137167] using wordTrace_append hprefix tailTrace_4137167
  have hstable : (prefixWord ++ tailWord_4137167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137167).length < 2 ^ (prefixWord ++ tailWord_4137167).sum := by decide
  have hdescent : baseEnd_4137167 < baseStart_4137167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137177 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 7]
def baseStart_4137177 : Nat := 118140960795 + 4137177 * 2 ^ 59
def prefixEnd_4137177 : Nat := 4983230072969 + 3 ^ 40 * 4137177 * 2
def baseEnd_4137177 : Nat := 236040039302918334406775

theorem tailTrace_4137177 : CollatzResearch.WordTrace tailWord_4137177 prefixEnd_4137177 236040039302918334406775 := by
  unfold tailWord_4137177
  simp only [CollatzResearch.WordTrace]
  refine ⟨150895241732721777423513785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100596827821814518282342523 150895241732721777423513785)
  ·
    refine ⟨113171431299541333067635339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150895241732721777423513785 113171431299541333067635339)
    ·
      refine ⟨169757146949311999601453009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113171431299541333067635339 169757146949311999601453009)
      ·
        refine ⟨127317860211983999701089757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169757146949311999601453009 127317860211983999701089757)
        ·
          refine ⟨47744197579493999887908659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127317860211983999701089757 47744197579493999887908659)
          ·
            refine ⟨71616296369240999831862989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47744197579493999887908659 71616296369240999831862989)
            ·
              refine ⟨26856111138465374936948621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71616296369240999831862989 26856111138465374936948621)
              ·
                refine ⟨10071041676924515601355733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26856111138465374936948621 10071041676924515601355733)
                ·
                  refine ⟨236040039302918334406775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10071041676924515601355733 236040039302918334406775)
                  ·
                    rfl

theorem cell23_4137177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_4137177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137177 prefixEnd_4137177 := by exact prefixLift 4137177
  have htrace : WordTrace (prefixWord ++ tailWord_4137177) baseStart_4137177 baseEnd_4137177 := by
    simpa [prefixWord, tailWord_4137177, baseEnd_4137177] using wordTrace_append hprefix tailTrace_4137177
  have hstable : (prefixWord ++ tailWord_4137177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137177).length < 2 ^ (prefixWord ++ tailWord_4137177).sum := by decide
  have hdescent : baseEnd_4137177 < baseStart_4137177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137224 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_4137224 : Nat := 118140960795 + 4137224 * 2 ^ 59
def prefixEnd_4137224 : Nat := 4983230072969 + 3 ^ 40 * 4137224 * 2
def baseEnd_4137224 : Nat := 708128162439008775257753

theorem tailTrace_4137224 : CollatzResearch.WordTrace tailWord_4137224 prefixEnd_4137224 708128162439008775257753 := by
  unfold tailWord_4137224
  simp only [CollatzResearch.WordTrace]
  refine ⟨75448477981775752225237363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100597970642367669633649817 75448477981775752225237363)
  ·
    refine ⟨113172716972663628337856045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75448477981775752225237363 113172716972663628337856045)
    ·
      refine ⟨42439768864748860626696017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113172716972663628337856045 42439768864748860626696017)
      ·
        refine ⟨31829826648561645470022013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42439768864748860626696017 31829826648561645470022013)
        ·
          refine ⟨11936184993210617051258255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31829826648561645470022013 11936184993210617051258255)
          ·
            refine ⟨17904277489815925576887383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936184993210617051258255 17904277489815925576887383)
            ·
              refine ⟨26856416234723888365331075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17904277489815925576887383 26856416234723888365331075)
              ·
                refine ⟨40284624352085832547996613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26856416234723888365331075 40284624352085832547996613)
                ·
                  refine ⟨7553367066016093602749365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40284624352085832547996613 7553367066016093602749365)
                  ·
                    refine ⟨708128162439008775257753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7553367066016093602749365 708128162439008775257753)
                    ·
                      rfl

theorem cell23_4137224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_4137224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137224 prefixEnd_4137224 := by exact prefixLift 4137224
  have htrace : WordTrace (prefixWord ++ tailWord_4137224) baseStart_4137224 baseEnd_4137224 := by
    simpa [prefixWord, tailWord_4137224, baseEnd_4137224] using wordTrace_append hprefix tailTrace_4137224
  have hstable : (prefixWord ++ tailWord_4137224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137224).length < 2 ^ (prefixWord ++ tailWord_4137224).sum := by decide
  have hdescent : baseEnd_4137224 < baseStart_4137224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137244 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4137244 : Nat := 118140960795 + 4137244 * 2 ^ 59
def prefixEnd_4137244 : Nat := 4983230072969 + 3 ^ 40 * 4137244 * 2
def baseEnd_4137244 : Nat := 2124394756930116247523167

theorem tailTrace_4137244 : CollatzResearch.WordTrace tailWord_4137244 prefixEnd_4137244 2124394756930116247523167 := by
  unfold tailWord_4137244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75448842711739523933101393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100598456948986031910801857 75448842711739523933101393)
  ·
    refine ⟨56586632033804642949826045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75448842711739523933101393 56586632033804642949826045)
    ·
      refine ⟨21219987012676741106184767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56586632033804642949826045 21219987012676741106184767)
      ·
        refine ⟨31829980519015111659277151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21219987012676741106184767 31829980519015111659277151)
        ·
          refine ⟨47744970778522667488915727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31829980519015111659277151 47744970778522667488915727)
          ·
            refine ⟨71617456167784001233373591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47744970778522667488915727 71617456167784001233373591)
            ·
              refine ⟨107426184251676001850060387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71617456167784001233373591 107426184251676001850060387)
              ·
                refine ⟨161139276377514002775090581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107426184251676001850060387 161139276377514002775090581)
                ·
                  refine ⟨7553403580195968880082371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161139276377514002775090581 7553403580195968880082371)
                  ·
                    refine ⟨11330105370293953320123557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553403580195968880082371 11330105370293953320123557)
                    ·
                      refine ⟨2124394756930116247523167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11330105370293953320123557 2124394756930116247523167)
                      ·
                        rfl

theorem cell23_4137244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4137244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137244 prefixEnd_4137244 := by exact prefixLift 4137244
  have htrace : WordTrace (prefixWord ++ tailWord_4137244) baseStart_4137244 baseEnd_4137244 := by
    simpa [prefixWord, tailWord_4137244, baseEnd_4137244] using wordTrace_append hprefix tailTrace_4137244
  have hstable : (prefixWord ++ tailWord_4137244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137244).length < 2 ^ (prefixWord ++ tailWord_4137244).sum := by decide
  have hdescent : baseEnd_4137244 < baseStart_4137244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137258 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4137258 : Nat := 118140960795 + 4137258 * 2 ^ 59
def prefixEnd_4137258 : Nat := 4983230072969 + 3 ^ 40 * 4137258 * 2
def baseEnd_4137258 : Nat := 708133981886426397582701

theorem tailTrace_4137258 : CollatzResearch.WordTrace tailWord_4137258 prefixEnd_4137258 708133981886426397582701 := by
  unfold tailWord_4137258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37724549011357082064303107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100598797363618885504808285 37724549011357082064303107)
  ·
    refine ⟨56586823517035623096454661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37724549011357082064303107 56586823517035623096454661)
    ·
      refine ⟨10610029409444179330585249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56586823517035623096454661 10610029409444179330585249)
      ·
        refine ⟨7957522057083134497938937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10610029409444179330585249 7957522057083134497938937)
        ·
          refine ⟨5968141542812350873454203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7957522057083134497938937 5968141542812350873454203)
          ·
            refine ⟨8952212314218526310181305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968141542812350873454203 8952212314218526310181305)
            ·
              refine ⟨6714159235663894732635979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8952212314218526310181305 6714159235663894732635979)
              ·
                refine ⟨10071238853495842098953969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714159235663894732635979 10071238853495842098953969)
                ·
                  refine ⟨7553429140121881574215477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10071238853495842098953969 7553429140121881574215477)
                  ·
                    refine ⟨708133981886426397582701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7553429140121881574215477 708133981886426397582701)
                    ·
                      rfl

theorem cell23_4137258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4137258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137258 prefixEnd_4137258 := by exact prefixLift 4137258
  have htrace : WordTrace (prefixWord ++ tailWord_4137258) baseStart_4137258 baseEnd_4137258 := by
    simpa [prefixWord, tailWord_4137258, baseEnd_4137258] using wordTrace_append hprefix tailTrace_4137258
  have hstable : (prefixWord ++ tailWord_4137258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137258).length < 2 ^ (prefixWord ++ tailWord_4137258).sum := by decide
  have hdescent : baseEnd_4137258 < baseStart_4137258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137311 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 3]
def baseStart_4137311 : Nat := 118140960795 + 4137311 * 2 ^ 59
def prefixEnd_4137311 : Nat := 4983230072969 + 3 ^ 40 * 4137311 * 2
def baseEnd_4137311 : Nat := 2124429160133967485385359

theorem tailTrace_4137311 : CollatzResearch.WordTrace tailWord_4137311 prefixEnd_4137311 2124429160133967485385359 := by
  unfold tailWord_4137311
  simp only [CollatzResearch.WordTrace]
  refine ⟨150900129114236318308891787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100600086076157545539261191 150900129114236318308891787)
  ·
    refine ⟨226350193671354477463337681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150900129114236318308891787 226350193671354477463337681)
    ·
      refine ⟨169762645253515858097503261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226350193671354477463337681 169762645253515858097503261)
      ·
        refine ⟨63660991970068446786563723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169762645253515858097503261 63660991970068446786563723)
        ·
          refine ⟨95491487955102670179845585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63660991970068446786563723 95491487955102670179845585)
          ·
            refine ⟨71618615966327002634884189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95491487955102670179845585 71618615966327002634884189)
            ·
              refine ⟨26856980987372625988081571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71618615966327002634884189 26856980987372625988081571)
              ·
                refine ⟨40285471481058938982122357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26856980987372625988081571 40285471481058938982122357)
                ·
                  refine ⟨3776762951349275529573971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40285471481058938982122357 3776762951349275529573971)
                  ·
                    refine ⟨5665144427023913294360957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776762951349275529573971 5665144427023913294360957)
                    ·
                      refine ⟨2124429160133967485385359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665144427023913294360957 2124429160133967485385359)
                      ·
                        rfl

theorem cell23_4137311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_4137311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137311 prefixEnd_4137311 := by exact prefixLift 4137311
  have htrace : WordTrace (prefixWord ++ tailWord_4137311) baseStart_4137311 baseEnd_4137311 := by
    simpa [prefixWord, tailWord_4137311, baseEnd_4137311] using wordTrace_append hprefix tailTrace_4137311
  have hstable : (prefixWord ++ tailWord_4137311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137311).length < 2 ^ (prefixWord ++ tailWord_4137311).sum := by decide
  have hdescent : baseEnd_4137311 < baseStart_4137311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137321 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 5, 2]
def baseStart_4137321 : Nat := 118140960795 + 4137321 * 2 ^ 59
def prefixEnd_4137321 : Nat := 4983230072969 + 3 ^ 40 * 4137321 * 2
def baseEnd_4137321 : Nat := 2124434294940512446260313

theorem tailTrace_4137321 : CollatzResearch.WordTrace tailWord_4137321 prefixEnd_4137321 2124434294940512446260313 := by
  unfold tailWord_4137321
  simp only [CollatzResearch.WordTrace]
  refine ⟨150900493844200090016755817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100600329229466726677837211 150900493844200090016755817)
  ·
    refine ⟨113175370383150067512566863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150900493844200090016755817 113175370383150067512566863)
    ·
      refine ⟨169763055574725101268850295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113175370383150067512566863 169763055574725101268850295)
      ·
        refine ⟨254644583362087651903275443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169763055574725101268850295 254644583362087651903275443)
        ·
          refine ⟨381966875043131477854913165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254644583362087651903275443 381966875043131477854913165)
          ·
            refine ⟨143237578141174304195592437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381966875043131477854913165 143237578141174304195592437)
            ·
              refine ⟨13428522950735091018336791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143237578141174304195592437 13428522950735091018336791)
              ·
                refine ⟨20142784426102636527505187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13428522950735091018336791 20142784426102636527505187)
                ·
                  refine ⟨30214176639153954791257781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20142784426102636527505187 30214176639153954791257781)
                  ·
                    refine ⟨2832579059920683261680417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30214176639153954791257781 2832579059920683261680417)
                    ·
                      refine ⟨2124434294940512446260313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832579059920683261680417 2124434294940512446260313)
                      ·
                        rfl

theorem cell23_4137321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5, 2].length) (baseStart_4137321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137321 prefixEnd_4137321 := by exact prefixLift 4137321
  have htrace : WordTrace (prefixWord ++ tailWord_4137321) baseStart_4137321 baseEnd_4137321 := by
    simpa [prefixWord, tailWord_4137321, baseEnd_4137321] using wordTrace_append hprefix tailTrace_4137321
  have hstable : (prefixWord ++ tailWord_4137321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137321).length < 2 ^ (prefixWord ++ tailWord_4137321).sum := by decide
  have hdescent : baseEnd_4137321 < baseStart_4137321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137345 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4137345 : Nat := 118140960795 + 4137345 * 2 ^ 59
def prefixEnd_4137345 : Nat := 4983230072969 + 3 ^ 40 * 4137345 * 2
def baseEnd_4137345 : Nat := 2124446618476220352360203

theorem tailTrace_4137345 : CollatzResearch.WordTrace tailWord_4137345 prefixEnd_4137345 2124446618476220352360203 := by
  unfold tailWord_4137345
  simp only [CollatzResearch.WordTrace]
  refine ⟨150901369196113142115629489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100600912797408761410419659 150901369196113142115629489)
  ·
    refine ⟨113176026897084856586722117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150901369196113142115629489 113176026897084856586722117)
    ·
      refine ⟨21220505043203410610010397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113176026897084856586722117 21220505043203410610010397)
      ·
        refine ⟨7957689391201278978753899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21220505043203410610010397 7957689391201278978753899)
        ·
          refine ⟨11936534086801918468130849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957689391201278978753899 11936534086801918468130849)
          ·
            refine ⟨8952400565101438851098137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11936534086801918468130849 8952400565101438851098137)
            ·
              refine ⟨6714300423826079138323603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8952400565101438851098137 6714300423826079138323603)
              ·
                refine ⟨10071450635739118707485405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714300423826079138323603 10071450635739118707485405)
                ·
                  refine ⟨3776793988402169515307027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10071450635739118707485405 3776793988402169515307027)
                  ·
                    refine ⟨5665190982603254272960541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776793988402169515307027 5665190982603254272960541)
                    ·
                      refine ⟨2124446618476220352360203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665190982603254272960541 2124446618476220352360203)
                      ·
                        rfl

theorem cell23_4137345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4137345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137345 prefixEnd_4137345 := by exact prefixLift 4137345
  have htrace : WordTrace (prefixWord ++ tailWord_4137345) baseStart_4137345 baseEnd_4137345 := by
    simpa [prefixWord, tailWord_4137345, baseEnd_4137345] using wordTrace_append hprefix tailTrace_4137345
  have hstable : (prefixWord ++ tailWord_4137345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137345).length < 2 ^ (prefixWord ++ tailWord_4137345).sum := by decide
  have hdescent : baseEnd_4137345 < baseStart_4137345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137368 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4137368 : Nat := 118140960795 + 4137368 * 2 ^ 59
def prefixEnd_4137368 : Nat := 4983230072969 + 3 ^ 40 * 4137368 * 2
def baseEnd_4137368 : Nat := 2124458428531273762372597

theorem tailTrace_4137368 : CollatzResearch.WordTrace tailWord_4137368 prefixEnd_4137368 2124458428531273762372597 := by
  unfold tailWord_4137368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75451104037514908521858379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100601472050019878029144505 75451104037514908521858379)
  ·
    refine ⟨113176656056272362782787569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75451104037514908521858379 113176656056272362782787569)
    ·
      refine ⟨84882492042204272087090677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113176656056272362782787569 84882492042204272087090677)
      ·
        refine ⟨7957733628956650508164751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84882492042204272087090677 7957733628956650508164751)
        ·
          refine ⟨11936600443434975762247127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957733628956650508164751 11936600443434975762247127)
          ·
            refine ⟨17904900665152463643370691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936600443434975762247127 17904900665152463643370691)
            ·
              refine ⟨26857350997728695465056037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17904900665152463643370691 26857350997728695465056037)
              ·
                refine ⟨5035753312074130399698007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26857350997728695465056037 5035753312074130399698007)
                ·
                  refine ⟨7553629968111195599547011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035753312074130399698007 7553629968111195599547011)
                  ·
                    refine ⟨11330444952166793399320517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553629968111195599547011 11330444952166793399320517)
                    ·
                      refine ⟨2124458428531273762372597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11330444952166793399320517 2124458428531273762372597)
                      ·
                        rfl

theorem cell23_4137368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4137368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137368 prefixEnd_4137368 := by exact prefixLift 4137368
  have htrace : WordTrace (prefixWord ++ tailWord_4137368) baseStart_4137368 baseEnd_4137368 := by
    simpa [prefixWord, tailWord_4137368, baseEnd_4137368] using wordTrace_append hprefix tailTrace_4137368
  have hstable : (prefixWord ++ tailWord_4137368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137368).length < 2 ^ (prefixWord ++ tailWord_4137368).sum := by decide
  have hdescent : baseEnd_4137368 < baseStart_4137368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137396 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4137396 : Nat := 118140960795 + 4137396 * 2 ^ 59
def prefixEnd_4137396 : Nat := 4983230072969 + 3 ^ 40 * 4137396 * 2
def baseEnd_4137396 : Nat := 2124472805989599652822469

theorem tailTrace_4137396 : CollatzResearch.WordTrace tailWord_4137396 prefixEnd_4137396 2124472805989599652822469 := by
  unfold tailWord_4137396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75451614659464188912868021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100602152879285585217157361 75451614659464188912868021)
  ·
    refine ⟨7073588874324767710581377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75451614659464188912868021 7073588874324767710581377)
    ·
      refine ⟨5305191655743575782936033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7073588874324767710581377 5305191655743575782936033)
      ·
        refine ⟨3978893741807681837202025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5305191655743575782936033 3978893741807681837202025)
        ·
          refine ⟨2984170306355761377901519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3978893741807681837202025 2984170306355761377901519)
          ·
            refine ⟨4476255459533642066852279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984170306355761377901519 4476255459533642066852279)
            ·
              refine ⟨6714383189300463100278419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476255459533642066852279 6714383189300463100278419)
              ·
                refine ⟨10071574783950694650417629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714383189300463100278419 10071574783950694650417629)
                ·
                  refine ⟨3776840543981510493906611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10071574783950694650417629 3776840543981510493906611)
                  ·
                    refine ⟨5665260815972265740859917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776840543981510493906611 5665260815972265740859917)
                    ·
                      refine ⟨2124472805989599652822469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665260815972265740859917 2124472805989599652822469)
                      ·
                        rfl

theorem cell23_4137396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4137396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137396 prefixEnd_4137396 := by exact prefixLift 4137396
  have htrace : WordTrace (prefixWord ++ tailWord_4137396) baseStart_4137396 baseEnd_4137396 := by
    simpa [prefixWord, tailWord_4137396, baseEnd_4137396] using wordTrace_append hprefix tailTrace_4137396
  have hstable : (prefixWord ++ tailWord_4137396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137396).length < 2 ^ (prefixWord ++ tailWord_4137396).sum := by decide
  have hdescent : baseEnd_4137396 < baseStart_4137396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137411 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 7, 2]
def baseStart_4137411 : Nat := 118140960795 + 4137411 * 2 ^ 59
def prefixEnd_4137411 : Nat := 4983230072969 + 3 ^ 40 * 4137411 * 2
def baseEnd_4137411 : Nat := 2124480508199417094134899

theorem tailTrace_4137411 : CollatzResearch.WordTrace tailWord_4137411 prefixEnd_4137411 2124480508199417094134899 := by
  unfold tailWord_4137411
  simp only [CollatzResearch.WordTrace]
  refine ⟨150903776413874035387532087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100602517609249356925021391 150903776413874035387532087)
  ·
    refine ⟨226355664620811053081298131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150903776413874035387532087 226355664620811053081298131)
    ·
      refine ⟨339533496931216579621947197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226355664620811053081298131 339533496931216579621947197)
      ·
        refine ⟨127325061349206217358230199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339533496931216579621947197 127325061349206217358230199)
        ·
          refine ⟨190987592023809326037345299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127325061349206217358230199 190987592023809326037345299)
          ·
            refine ⟨286481388035713989056017949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190987592023809326037345299 286481388035713989056017949)
            ·
              refine ⟨107430520513392745896006731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286481388035713989056017949 107430520513392745896006731)
              ·
                refine ⟨161145780770089118844010097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107430520513392745896006731 161145780770089118844010097)
                ·
                  refine ⟨120859335577566839133007573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161145780770089118844010097 120859335577566839133007573)
                  ·
                    refine ⟨2832640677599222792179865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 120859335577566839133007573 2832640677599222792179865)
                    ·
                      refine ⟨2124480508199417094134899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832640677599222792179865 2124480508199417094134899)
                      ·
                        rfl

theorem cell23_4137411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_4137411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137411 prefixEnd_4137411 := by exact prefixLift 4137411
  have htrace : WordTrace (prefixWord ++ tailWord_4137411) baseStart_4137411 baseEnd_4137411 := by
    simpa [prefixWord, tailWord_4137411, baseEnd_4137411] using wordTrace_append hprefix tailTrace_4137411
  have hstable : (prefixWord ++ tailWord_4137411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137411).length < 2 ^ (prefixWord ++ tailWord_4137411).sum := by decide
  have hdescent : baseEnd_4137411 < baseStart_4137411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137471 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_4137471 : Nat := 118140960795 + 4137471 * 2 ^ 59
def prefixEnd_4137471 : Nat := 4983230072969 + 3 ^ 40 * 4137471 * 2
def baseEnd_4137471 : Nat := 2124511317038686859384623

theorem tailTrace_4137471 : CollatzResearch.WordTrace tailWord_4137471 prefixEnd_4137471 2124511317038686859384623 := by
  unfold tailWord_4137471
  simp only [CollatzResearch.WordTrace]
  refine ⟨150905964793656665634716267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100603976529104443756477511 150905964793656665634716267)
  ·
    refine ⟨226358947190484998452074401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150905964793656665634716267 226358947190484998452074401)
    ·
      refine ⟨169769210392863748839055801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226358947190484998452074401 169769210392863748839055801)
      ·
        refine ⟨127326907794647811629291851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169769210392863748839055801 127326907794647811629291851)
        ·
          refine ⟨190990361691971717443937777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127326907794647811629291851 190990361691971717443937777)
          ·
            refine ⟨143242771268978788082953333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190990361691971717443937777 143242771268978788082953333)
            ·
              refine ⟨13429009806466761382776875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143242771268978788082953333 13429009806466761382776875)
              ·
                refine ⟨20143514709700142074165313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429009806466761382776875 20143514709700142074165313)
                ·
                  refine ⟨15107636032275106555623985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20143514709700142074165313 15107636032275106555623985)
                  ·
                    refine ⟨11330727024206329916717989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15107636032275106555623985 11330727024206329916717989)
                    ·
                      refine ⟨2124511317038686859384623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11330727024206329916717989 2124511317038686859384623)
                      ·
                        rfl

theorem cell23_4137471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_4137471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137471 prefixEnd_4137471 := by exact prefixLift 4137471
  have htrace : WordTrace (prefixWord ++ tailWord_4137471) baseStart_4137471 baseEnd_4137471 := by
    simpa [prefixWord, tailWord_4137471, baseEnd_4137471] using wordTrace_append hprefix tailTrace_4137471
  have hstable : (prefixWord ++ tailWord_4137471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137471).length < 2 ^ (prefixWord ++ tailWord_4137471).sum := by decide
  have hdescent : baseEnd_4137471 < baseStart_4137471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137475 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 2, 2, 2]
def baseStart_4137475 : Nat := 118140960795 + 4137475 * 2 ^ 59
def prefixEnd_4137475 : Nat := 4983230072969 + 3 ^ 40 * 4137475 * 2
def baseEnd_4137475 : Nat := 2124513370961304843734605

theorem tailTrace_4137475 : CollatzResearch.WordTrace tailWord_4137475 prefixEnd_4137475 2124513370961304843734605 := by
  unfold tailWord_4137475
  simp only [CollatzResearch.WordTrace]
  refine ⟨150906110685642174317861879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100604073790428116211907919 150906110685642174317861879)
  ·
    refine ⟨226359166028463261476792819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150906110685642174317861879 226359166028463261476792819)
    ·
      refine ⟨339538749042694892215189229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226359166028463261476792819 339538749042694892215189229)
      ·
        refine ⟨127327030891010584580695961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339538749042694892215189229 127327030891010584580695961)
        ·
          refine ⟨95495273168257938435521971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127327030891010584580695961 95495273168257938435521971)
          ·
            refine ⟨143242909752386907653282957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95495273168257938435521971 143242909752386907653282957)
            ·
              refine ⟨53716091157145090369981109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143242909752386907653282957 53716091157145090369981109)
              ·
                refine ⟨5035883545982352222185729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53716091157145090369981109 5035883545982352222185729)
                ·
                  refine ⟨3776912659486764166639297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5035883545982352222185729 3776912659486764166639297)
                  ·
                    refine ⟨2832684494615073124979473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776912659486764166639297 2832684494615073124979473)
                    ·
                      refine ⟨2124513370961304843734605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832684494615073124979473 2124513370961304843734605)
                      ·
                        rfl

theorem cell23_4137475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_4137475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137475 prefixEnd_4137475 := by exact prefixLift 4137475
  have htrace : WordTrace (prefixWord ++ tailWord_4137475) baseStart_4137475 baseEnd_4137475 := by
    simpa [prefixWord, tailWord_4137475, baseEnd_4137475] using wordTrace_append hprefix tailTrace_4137475
  have hstable : (prefixWord ++ tailWord_4137475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137475).length < 2 ^ (prefixWord ++ tailWord_4137475).sum := by decide
  have hdescent : baseEnd_4137475 < baseStart_4137475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137491 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3]
def baseStart_4137491 : Nat := 118140960795 + 4137491 * 2 ^ 59
def prefixEnd_4137491 : Nat := 4983230072969 + 3 ^ 40 * 4137491 * 2
def baseEnd_4137491 : Nat := 2124521586651776781134531

theorem tailTrace_4137491 : CollatzResearch.WordTrace tailWord_4137491 prefixEnd_4137491 2124521586651776781134531 := by
  unfold tailWord_4137491
  simp only [CollatzResearch.WordTrace]
  refine ⟨150906694253584209050444327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100604462835722806033629551 150906694253584209050444327)
  ·
    refine ⟨226360041380376313575666491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150906694253584209050444327 226360041380376313575666491)
    ·
      refine ⟨339540062070564470363499737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226360041380376313575666491 339540062070564470363499737)
      ·
        refine ⟨254655046552923352772624803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339540062070564470363499737 254655046552923352772624803)
        ·
          refine ⟨381982569829385029158937205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254655046552923352772624803 381982569829385029158937205)
          ·
            refine ⟨35810865921504846483650363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 381982569829385029158937205 35810865921504846483650363)
            ·
              refine ⟨53716298882257269725475545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35810865921504846483650363 53716298882257269725475545)
              ·
                refine ⟨40287224161692952294106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53716298882257269725475545 40287224161692952294106659)
                ·
                  refine ⟨60430836242539428441159989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40287224161692952294106659 60430836242539428441159989)
                  ·
                    refine ⟨5665390897738071416358749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60430836242539428441159989 5665390897738071416358749)
                    ·
                      refine ⟨2124521586651776781134531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665390897738071416358749 2124521586651776781134531)
                      ·
                        rfl

theorem cell23_4137491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_4137491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137491 prefixEnd_4137491 := by exact prefixLift 4137491
  have htrace : WordTrace (prefixWord ++ tailWord_4137491) baseStart_4137491 baseEnd_4137491 := by
    simpa [prefixWord, tailWord_4137491, baseEnd_4137491] using wordTrace_append hprefix tailTrace_4137491
  have hstable : (prefixWord ++ tailWord_4137491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137491).length < 2 ^ (prefixWord ++ tailWord_4137491).sum := by decide
  have hdescent : baseEnd_4137491 < baseStart_4137491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137492 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4137492 : Nat := 118140960795 + 4137492 * 2 ^ 59
def prefixEnd_4137492 : Nat := 4983230072969 + 3 ^ 40 * 4137492 * 2
def baseEnd_4137492 : Nat := 2124522100132431277222027

theorem tailTrace_4137492 : CollatzResearch.WordTrace tailWord_4137492 prefixEnd_4137492 2124522100132431277222027 := by
  unfold tailWord_4137492
  simp only [CollatzResearch.WordTrace]
  refine ⟨75453365363290293110615365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100604487151053724147487153 75453365363290293110615365)
  ·
    refine ⟨14147506005616929958240381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75453365363290293110615365 14147506005616929958240381)
    ·
      refine ⟨5305314752106348734340143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14147506005616929958240381 5305314752106348734340143)
      ·
        refine ⟨7957972128159523101510215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305314752106348734340143 7957972128159523101510215)
        ·
          refine ⟨11936958192239284652265323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957972128159523101510215 11936958192239284652265323)
          ·
            refine ⟨17905437288358926978397985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936958192239284652265323 17905437288358926978397985)
            ·
              refine ⟨13429077966269195233798489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17905437288358926978397985 13429077966269195233798489)
              ·
                refine ⟨10071808474701896425348867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13429077966269195233798489 10071808474701896425348867)
                ·
                  refine ⟨15107712712052844638023301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10071808474701896425348867 15107712712052844638023301)
                  ·
                    refine ⟨2832696133509908369629369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15107712712052844638023301 2832696133509908369629369)
                    ·
                      refine ⟨2124522100132431277222027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832696133509908369629369 2124522100132431277222027)
                      ·
                        rfl

theorem cell23_4137492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4137492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137492 prefixEnd_4137492 := by exact prefixLift 4137492
  have htrace : WordTrace (prefixWord ++ tailWord_4137492) baseStart_4137492 baseEnd_4137492 := by
    simpa [prefixWord, tailWord_4137492, baseEnd_4137492] using wordTrace_append hprefix tailTrace_4137492
  have hstable : (prefixWord ++ tailWord_4137492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137492).length < 2 ^ (prefixWord ++ tailWord_4137492).sum := by decide
  have hdescent : baseEnd_4137492 < baseStart_4137492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137498 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_4137498 : Nat := 118140960795 + 4137498 * 2 ^ 59
def prefixEnd_4137498 : Nat := 4983230072969 + 3 ^ 40 * 4137498 * 2
def baseEnd_4137498 : Nat := 236058353446262028194111

theorem tailTrace_4137498 : CollatzResearch.WordTrace tailWord_4137498 prefixEnd_4137498 236058353446262028194111 := by
  unfold tailWord_4137498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726737391139712311487287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100604633043039232830632765 37726737391139712311487287)
  ·
    refine ⟨56590106086709568467230931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37726737391139712311487287 56590106086709568467230931)
    ·
      refine ⟨84885159130064352700846397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56590106086709568467230931 84885159130064352700846397)
      ·
        refine ⟨31831934673774132262817399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84885159130064352700846397 31831934673774132262817399)
        ·
          refine ⟨47747902010661198394226099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31831934673774132262817399 47747902010661198394226099)
          ·
            refine ⟨71621853015991797591339149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47747902010661198394226099 71621853015991797591339149)
            ·
              refine ⟨26858194880996924096752181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71621853015991797591339149 26858194880996924096752181)
              ·
                refine ⟨2517955770093461634070517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26858194880996924096752181 2517955770093461634070517)
                ·
                  refine ⟨236058353446262028194111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2517955770093461634070517 236058353446262028194111)
                  ·
                    rfl

theorem cell23_4137498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_4137498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137498 prefixEnd_4137498 := by exact prefixLift 4137498
  have htrace : WordTrace (prefixWord ++ tailWord_4137498) baseStart_4137498 baseEnd_4137498 := by
    simpa [prefixWord, tailWord_4137498, baseEnd_4137498] using wordTrace_append hprefix tailTrace_4137498
  have hstable : (prefixWord ++ tailWord_4137498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137498).length < 2 ^ (prefixWord ++ tailWord_4137498).sum := by decide
  have hdescent : baseEnd_4137498 < baseStart_4137498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137521 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4137521 : Nat := 118140960795 + 4137521 * 2 ^ 59
def prefixEnd_4137521 : Nat := 4983230072969 + 3 ^ 40 * 4137521 * 2
def baseEnd_4137521 : Nat := 2124536991071411663759393

theorem tailTrace_4137521 : CollatzResearch.WordTrace tailWord_4137521 prefixEnd_4137521 2124536991071411663759393 := by
  unfold tailWord_4137521
  simp only [CollatzResearch.WordTrace]
  refine ⟨150907788443475524174036417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100605192295650349449357611 150907788443475524174036417)
  ·
    refine ⟨113180841332606643130527313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150907788443475524174036417 113180841332606643130527313)
    ·
      refine ⟨84885630999454982347895485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113180841332606643130527313 84885630999454982347895485)
      ·
        refine ⟨31832111624795618380460807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84885630999454982347895485 31832111624795618380460807)
        ·
          refine ⟨47748167437193427570691211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31832111624795618380460807 47748167437193427570691211)
          ·
            refine ⟨71622251155790141356036817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47748167437193427570691211 71622251155790141356036817)
            ·
              refine ⟨53716688366842606017027613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71622251155790141356036817 53716688366842606017027613)
              ·
                refine ⟨20143758137565977256385355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53716688366842606017027613 20143758137565977256385355)
                ·
                  refine ⟨30215637206348965884578033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20143758137565977256385355 30215637206348965884578033)
                  ·
                    refine ⟨22661727904761724413433525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30215637206348965884578033 22661727904761724413433525)
                    ·
                      refine ⟨2124536991071411663759393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22661727904761724413433525 2124536991071411663759393)
                      ·
                        rfl

theorem cell23_4137521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4137521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137521 prefixEnd_4137521 := by exact prefixLift 4137521
  have htrace : WordTrace (prefixWord ++ tailWord_4137521) baseStart_4137521 baseEnd_4137521 := by
    simpa [prefixWord, tailWord_4137521, baseEnd_4137521] using wordTrace_append hprefix tailTrace_4137521
  have hstable : (prefixWord ++ tailWord_4137521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137521).length < 2 ^ (prefixWord ++ tailWord_4137521).sum := by decide
  have hdescent : baseEnd_4137521 < baseStart_4137521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137526 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4137526 : Nat := 118140960795 + 4137526 * 2 ^ 59
def prefixEnd_4137526 : Nat := 4983230072969 + 3 ^ 40 * 4137526 * 2
def baseEnd_4137526 : Nat := 2124539558474684144196871

theorem tailTrace_4137526 : CollatzResearch.WordTrace tailWord_4137526 prefixEnd_4137526 2124539558474684144196871 := by
  unfold tailWord_4137526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431748175528588126748027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100605313872304940018645621 9431748175528588126748027)
  ·
    refine ⟨14147622263292882190122041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9431748175528588126748027 14147622263292882190122041)
    ·
      refine ⟨10610716697469661642591531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14147622263292882190122041 10610716697469661642591531)
      ·
        refine ⟨15916075046204492463887297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10610716697469661642591531 15916075046204492463887297)
        ·
          refine ⟨11937056284653369347915473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15916075046204492463887297 11937056284653369347915473)
          ·
            refine ⟨8952792213490027010936605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11937056284653369347915473 8952792213490027010936605)
            ·
              refine ⟨3357297080058760129101227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8952792213490027010936605 3357297080058760129101227)
              ·
                refine ⟨5035945620088140193651841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357297080058760129101227 5035945620088140193651841)
                ·
                  refine ⟨3776959215066105145238881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5035945620088140193651841 3776959215066105145238881)
                  ·
                    refine ⟨2832719411299578858929161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776959215066105145238881 2832719411299578858929161)
                    ·
                      refine ⟨2124539558474684144196871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832719411299578858929161 2124539558474684144196871)
                      ·
                        rfl

theorem cell23_4137526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4137526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137526 prefixEnd_4137526 := by exact prefixLift 4137526
  have htrace : WordTrace (prefixWord ++ tailWord_4137526) baseStart_4137526 baseEnd_4137526 := by
    simpa [prefixWord, tailWord_4137526, baseEnd_4137526] using wordTrace_append hprefix tailTrace_4137526
  have hstable : (prefixWord ++ tailWord_4137526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137526).length < 2 ^ (prefixWord ++ tailWord_4137526).sum := by decide
  have hdescent : baseEnd_4137526 < baseStart_4137526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137548 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4137548 : Nat := 118140960795 + 4137548 * 2 ^ 59
def prefixEnd_4137548 : Nat := 4983230072969 + 3 ^ 40 * 4137548 * 2
def baseEnd_4137548 : Nat := 2124550855049083058121769

theorem tailTrace_4137548 : CollatzResearch.WordTrace tailWord_4137548 prefixEnd_4137548 2124550855049083058121769 := by
  unfold tailWord_4137548
  simp only [CollatzResearch.WordTrace]
  refine ⟨75454386607188853892634649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100605848809585138523512865 75454386607188853892634649)
  ·
    refine ⟨56590789955391640419475987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75454386607188853892634649 56590789955391640419475987)
    ·
      refine ⟨84886184933087460629213981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56590789955391640419475987 84886184933087460629213981)
      ·
        refine ⟨31832319349907797735955243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84886184933087460629213981 31832319349907797735955243)
        ·
          refine ⟨47748479024861696603932865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31832319349907797735955243 47748479024861696603932865)
          ·
            refine ⟨35811359268646272452949649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47748479024861696603932865 35811359268646272452949649)
            ·
              refine ⟨26858519451484704339712237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35811359268646272452949649 26858519451484704339712237)
              ·
                refine ⟨10071944794306764127392089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26858519451484704339712237 10071944794306764127392089)
                ·
                  refine ⟨7553958595730073095544067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10071944794306764127392089 7553958595730073095544067)
                  ·
                    refine ⟨11330937893595109643316101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553958595730073095544067 11330937893595109643316101)
                    ·
                      refine ⟨2124550855049083058121769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11330937893595109643316101 2124550855049083058121769)
                      ·
                        rfl

theorem cell23_4137548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4137548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137548 prefixEnd_4137548 := by exact prefixLift 4137548
  have htrace : WordTrace (prefixWord ++ tailWord_4137548) baseStart_4137548 baseEnd_4137548 := by
    simpa [prefixWord, tailWord_4137548, baseEnd_4137548] using wordTrace_append hprefix tailTrace_4137548
  have hstable : (prefixWord ++ tailWord_4137548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137548).length < 2 ^ (prefixWord ++ tailWord_4137548).sum := by decide
  have hdescent : baseEnd_4137548 < baseStart_4137548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137566 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4137566 : Nat := 118140960795 + 4137566 * 2 ^ 59
def prefixEnd_4137566 : Nat := 4983230072969 + 3 ^ 40 * 4137566 * 2
def baseEnd_4137566 : Nat := 236062233077873776410743

theorem tailTrace_4137566 : CollatzResearch.WordTrace tailWord_4137566 prefixEnd_4137566 236062233077873776410743 := by
  unfold tailWord_4137566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863678716039062107428069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100606286485541664572949701 18863678716039062107428069)
  ·
    refine ⟨3536939759257324145142763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18863678716039062107428069 3536939759257324145142763)
    ·
      refine ⟨5305409638885986217714145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536939759257324145142763 5305409638885986217714145)
      ·
        refine ⟨3979057229164489663285609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5305409638885986217714145 3979057229164489663285609)
        ·
          refine ⟨2984292921873367247464207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979057229164489663285609 2984292921873367247464207)
          ·
            refine ⟨4476439382810050871196311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984292921873367247464207 4476439382810050871196311)
            ·
              refine ⟨6714659074215076306794467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476439382810050871196311 6714659074215076306794467)
              ·
                refine ⟨10071988611322614460191701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714659074215076306794467 10071988611322614460191701)
                ·
                  refine ⟨236062233077873776410743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10071988611322614460191701 236062233077873776410743)
                  ·
                    rfl

theorem cell23_4137566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4137566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137566 prefixEnd_4137566 := by exact prefixLift 4137566
  have htrace : WordTrace (prefixWord ++ tailWord_4137566) baseStart_4137566 baseEnd_4137566 := by
    simpa [prefixWord, tailWord_4137566, baseEnd_4137566] using wordTrace_append hprefix tailTrace_4137566
  have hstable : (prefixWord ++ tailWord_4137566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137566).length < 2 ^ (prefixWord ++ tailWord_4137566).sum := by decide
  have hdescent : baseEnd_4137566 < baseStart_4137566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137568 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_4137568 : Nat := 118140960795 + 4137568 * 2 ^ 59
def prefixEnd_4137568 : Nat := 4983230072969 + 3 ^ 40 * 4137568 * 2
def baseEnd_4137568 : Nat := 2124561124662172979871677

theorem tailTrace_4137568 : CollatzResearch.WordTrace tailWord_4137568 prefixEnd_4137568 2124561124662172979871677 := by
  unfold tailWord_4137568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75454751337152625600498679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100606335116203500800664905 75454751337152625600498679)
  ·
    refine ⟨113182127005728938400748019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75454751337152625600498679 113182127005728938400748019)
    ·
      refine ⟨169773190508593407601122029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113182127005728938400748019 169773190508593407601122029)
      ·
        refine ⟨63664946440722527850420761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169773190508593407601122029 63664946440722527850420761)
        ·
          refine ⟨47748709830541895887815571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63664946440722527850420761 47748709830541895887815571)
          ·
            refine ⟨71623064745812843831723357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47748709830541895887815571 71623064745812843831723357)
            ·
              refine ⟨26858649279679816436896259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71623064745812843831723357 26858649279679816436896259)
              ·
                refine ⟨40287973919519724655344389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26858649279679816436896259 40287973919519724655344389)
                ·
                  refine ⟨7553995109909948372877073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40287973919519724655344389 7553995109909948372877073)
                  ·
                    refine ⟨5665496332432461279657805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7553995109909948372877073 5665496332432461279657805)
                    ·
                      refine ⟨2124561124662172979871677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665496332432461279657805 2124561124662172979871677)
                      ·
                        rfl

theorem cell23_4137568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_4137568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137568 prefixEnd_4137568 := by exact prefixLift 4137568
  have htrace : WordTrace (prefixWord ++ tailWord_4137568) baseStart_4137568 baseEnd_4137568 := by
    simpa [prefixWord, tailWord_4137568, baseEnd_4137568] using wordTrace_append hprefix tailTrace_4137568
  have hstable : (prefixWord ++ tailWord_4137568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137568).length < 2 ^ (prefixWord ++ tailWord_4137568).sum := by decide
  have hdescent : baseEnd_4137568 < baseStart_4137568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137571 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 8]
def baseStart_4137571 : Nat := 118140960795 + 4137571 * 2 ^ 59
def prefixEnd_4137571 : Nat := 4983230072969 + 3 ^ 40 * 4137571 * 2
def baseEnd_4137571 : Nat := 236062518344904052014907

theorem tailTrace_4137571 : CollatzResearch.WordTrace tailWord_4137571 prefixEnd_4137571 236062518344904052014907 := by
  unfold tailWord_4137571
  simp only [CollatzResearch.WordTrace]
  refine ⟨150909612093294382713356567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100606408062196255142237711 150909612093294382713356567)
  ·
    refine ⟨226364418139941574070034851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150909612093294382713356567 226364418139941574070034851)
    ·
      refine ⟨339546627209912361105052277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226364418139941574070034851 339546627209912361105052277)
      ·
        refine ⟨31832496300929283853598651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339546627209912361105052277 31832496300929283853598651)
        ·
          refine ⟨47748744451393925780397977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31832496300929283853598651 47748744451393925780397977)
          ·
            refine ⟨35811558338545444335298483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47748744451393925780397977 35811558338545444335298483)
            ·
              refine ⟨53717337507818166502947725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35811558338545444335298483 53717337507818166502947725)
              ·
                refine ⟨20144001565431812438605397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53717337507818166502947725 20144001565431812438605397)
                ·
                  refine ⟨236062518344904052014907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20144001565431812438605397 236062518344904052014907)
                  ·
                    rfl

theorem cell23_4137571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 8].length) (baseStart_4137571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137571 prefixEnd_4137571 := by exact prefixLift 4137571
  have htrace : WordTrace (prefixWord ++ tailWord_4137571) baseStart_4137571 baseEnd_4137571 := by
    simpa [prefixWord, tailWord_4137571, baseEnd_4137571] using wordTrace_append hprefix tailTrace_4137571
  have hstable : (prefixWord ++ tailWord_4137571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137571).length < 2 ^ (prefixWord ++ tailWord_4137571).sum := by decide
  have hdescent : baseEnd_4137571 < baseStart_4137571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137591 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_4137591 : Nat := 118140960795 + 4137591 * 2 ^ 59
def prefixEnd_4137591 : Nat := 4983230072969 + 3 ^ 40 * 4137591 * 2
def baseEnd_4137591 : Nat := 2124572934717226389884071

theorem tailTrace_4137591 : CollatzResearch.WordTrace tailWord_4137591 prefixEnd_4137591 2124572934717226389884071 := by
  unfold tailWord_4137591
  simp only [CollatzResearch.WordTrace]
  refine ⟨150910341553221926129084627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100606894368814617419389751 150910341553221926129084627)
  ·
    refine ⟨226365512329832889193626941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150910341553221926129084627 226365512329832889193626941)
    ·
      refine ⟨84887067123687333447610103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226365512329832889193626941 84887067123687333447610103)
      ·
        refine ⟨127330600685531000171415155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84887067123687333447610103 127330600685531000171415155)
        ·
          refine ⟨190995901028296500257122733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127330600685531000171415155 190995901028296500257122733)
          ·
            refine ⟨71623462885611187596421025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190995901028296500257122733 71623462885611187596421025)
            ·
              refine ⟨53717597164208390697315769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71623462885611187596421025 53717597164208390697315769)
              ·
                refine ⟨40288197873156293022986827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53717597164208390697315769 40288197873156293022986827)
                ·
                  refine ⟨60432296809734439534480241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40288197873156293022986827 60432296809734439534480241)
                  ·
                    refine ⟨45324222607300829650860181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60432296809734439534480241 45324222607300829650860181)
                    ·
                      refine ⟨2124572934717226389884071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45324222607300829650860181 2124572934717226389884071)
                      ·
                        rfl

theorem cell23_4137591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_4137591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137591 prefixEnd_4137591 := by exact prefixLift 4137591
  have htrace : WordTrace (prefixWord ++ tailWord_4137591) baseStart_4137591 baseEnd_4137591 := by
    simpa [prefixWord, tailWord_4137591, baseEnd_4137591] using wordTrace_append hprefix tailTrace_4137591
  have hstable : (prefixWord ++ tailWord_4137591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137591).length < 2 ^ (prefixWord ++ tailWord_4137591).sum := by decide
  have hdescent : baseEnd_4137591 < baseStart_4137591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137611 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_4137611 : Nat := 118140960795 + 4137611 * 2 ^ 59
def prefixEnd_4137611 : Nat := 4983230072969 + 3 ^ 40 * 4137611 * 2
def baseEnd_4137611 : Nat := 2124583204330316311633979

theorem tailTrace_4137611 : CollatzResearch.WordTrace tailWord_4137611 prefixEnd_4137611 2124583204330316311633979 := by
  unfold tailWord_4137611
  simp only [CollatzResearch.WordTrace]
  refine ⟨150911071013149469544812687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100607380675432979696541791 150911071013149469544812687)
  ·
    refine ⟨226366606519724204317219031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150911071013149469544812687 226366606519724204317219031)
    ·
      refine ⟨339549909779586306475828547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226366606519724204317219031 339549909779586306475828547)
      ·
        refine ⟨509324864669379459713742821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339549909779586306475828547 509324864669379459713742821)
        ·
          refine ⟨95498412125508648696326779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509324864669379459713742821 95498412125508648696326779)
          ·
            refine ⟨143247618188262973044490169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95498412125508648696326779 143247618188262973044490169)
            ·
              refine ⟨107435713641197229783367627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143247618188262973044490169 107435713641197229783367627)
              ·
                refine ⟨161153570461795844675051441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107435713641197229783367627 161153570461795844675051441)
                ·
                  refine ⟨120865177846346883506288581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161153570461795844675051441 120865177846346883506288581)
                  ·
                    refine ⟨22662220846190040657429109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120865177846346883506288581 22662220846190040657429109)
                    ·
                      refine ⟨2124583204330316311633979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22662220846190040657429109 2124583204330316311633979)
                      ·
                        rfl

theorem cell23_4137611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_4137611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137611 prefixEnd_4137611 := by exact prefixLift 4137611
  have htrace : WordTrace (prefixWord ++ tailWord_4137611) baseStart_4137611 baseEnd_4137611 := by
    simpa [prefixWord, tailWord_4137611, baseEnd_4137611] using wordTrace_append hprefix tailTrace_4137611
  have hstable : (prefixWord ++ tailWord_4137611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137611).length < 2 ^ (prefixWord ++ tailWord_4137611).sum := by decide
  have hdescent : baseEnd_4137611 < baseStart_4137611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137625 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 2, 3, 2]
def baseStart_4137625 : Nat := 118140960795 + 4137625 * 2 ^ 59
def prefixEnd_4137625 : Nat := 4983230072969 + 3 ^ 40 * 4137625 * 2
def baseEnd_4137625 : Nat := 2124590393059479256858915

theorem tailTrace_4137625 : CollatzResearch.WordTrace tailWord_4137625 prefixEnd_4137625 2124590393059479256858915 := by
  unfold tailWord_4137625
  simp only [CollatzResearch.WordTrace]
  refine ⟨150911581635098749935822329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100607721090065833290548219 150911581635098749935822329)
  ·
    refine ⟨113183686226324062451866747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150911581635098749935822329 113183686226324062451866747)
    ·
      refine ⟨169775529339486093677800121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113183686226324062451866747 169775529339486093677800121)
      ·
        refine ⟨127331647004614570258350091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169775529339486093677800121 127331647004614570258350091)
        ·
          refine ⟨190997470506921855387525137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127331647004614570258350091 190997470506921855387525137)
          ·
            refine ⟨143248102880191391540643853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190997470506921855387525137 143248102880191391540643853)
            ·
              refine ⟨53718038580071771827741445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143248102880191391540643853 53718038580071771827741445)
              ·
                refine ⟨10072132233763457217701521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53718038580071771827741445 10072132233763457217701521)
                ·
                  refine ⟨7554099175322592913276141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072132233763457217701521 7554099175322592913276141)
                  ·
                    refine ⟨2832787190745972342478553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7554099175322592913276141 2832787190745972342478553)
                    ·
                      refine ⟨2124590393059479256858915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832787190745972342478553 2124590393059479256858915)
                      ·
                        rfl

theorem cell23_4137625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_4137625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137625 prefixEnd_4137625 := by exact prefixLift 4137625
  have htrace : WordTrace (prefixWord ++ tailWord_4137625) baseStart_4137625 baseEnd_4137625 := by
    simpa [prefixWord, tailWord_4137625, baseEnd_4137625] using wordTrace_append hprefix tailTrace_4137625
  have hstable : (prefixWord ++ tailWord_4137625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137625).length < 2 ^ (prefixWord ++ tailWord_4137625).sum := by decide
  have hdescent : baseEnd_4137625 < baseStart_4137625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137648 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_4137648 : Nat := 118140960795 + 4137648 * 2 ^ 59
def prefixEnd_4137648 : Nat := 4983230072969 + 3 ^ 40 * 4137648 * 2
def baseEnd_4137648 : Nat := 708200734371510888957103

theorem tailTrace_4137648 : CollatzResearch.WordTrace tailWord_4137648 prefixEnd_4137648 708200734371510888957103 := by
  unfold tailWord_4137648
  simp only [CollatzResearch.WordTrace]
  refine ⟨75456210257007712431954799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100608280342676949909273065 75456210257007712431954799)
  ·
    refine ⟨113184315385511568647932199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75456210257007712431954799 113184315385511568647932199)
    ·
      refine ⟨169776473078267352971898299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113184315385511568647932199 169776473078267352971898299)
      ·
        refine ⟨254664709617401029457847449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169776473078267352971898299 254664709617401029457847449)
        ·
          refine ⟨190998532213050772093385587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254664709617401029457847449 190998532213050772093385587)
          ·
            refine ⟨286497798319576158140078381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190998532213050772093385587 286497798319576158140078381)
            ·
              refine ⟨107436674369841059302529393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286497798319576158140078381 107436674369841059302529393)
              ·
                refine ⟨80577505777380794476897045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107436674369841059302529393 80577505777380794476897045)
                ·
                  refine ⟨3777070583314724741104549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80577505777380794476897045 3777070583314724741104549)
                  ·
                    refine ⟨708200734371510888957103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777070583314724741104549 708200734371510888957103)
                    ·
                      rfl

theorem cell23_4137648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_4137648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137648 prefixEnd_4137648 := by exact prefixLift 4137648
  have htrace : WordTrace (prefixWord ++ tailWord_4137648) baseStart_4137648 baseEnd_4137648 := by
    simpa [prefixWord, tailWord_4137648, baseEnd_4137648] using wordTrace_append hprefix tailTrace_4137648
  have hstable : (prefixWord ++ tailWord_4137648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137648).length < 2 ^ (prefixWord ++ tailWord_4137648).sum := by decide
  have hdescent : baseEnd_4137648 < baseStart_4137648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137649 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4137649 : Nat := 118140960795 + 4137649 * 2 ^ 59
def prefixEnd_4137649 : Nat := 4983230072969 + 3 ^ 40 * 4137649 * 2
def baseEnd_4137649 : Nat := 2124602716595187162958805

theorem tailTrace_4137649 : CollatzResearch.WordTrace tailWord_4137649 prefixEnd_4137649 2124602716595187162958805 := by
  unfold tailWord_4137649
  simp only [CollatzResearch.WordTrace]
  refine ⟨150912456987011802034696001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100608304658007868023130667 150912456987011802034696001)
  ·
    refine ⟨113184342740258851526022001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150912456987011802034696001 113184342740258851526022001)
    ·
      refine ⟨84888257055194138644516501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113184342740258851526022001 84888257055194138644516501)
      ·
        refine ⟨3979137049462225248961711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84888257055194138644516501 3979137049462225248961711)
        ·
          refine ⟨5968705574193337873442567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979137049462225248961711 5968705574193337873442567)
          ·
            refine ⟨8953058361290006810163851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968705574193337873442567 8953058361290006810163851)
            ·
              refine ⟨13429587541935010215245777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953058361290006810163851 13429587541935010215245777)
              ·
                refine ⟨10072190656451257661434333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13429587541935010215245777 10072190656451257661434333)
                ·
                  refine ⟨3777071496169221623037875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10072190656451257661434333 3777071496169221623037875)
                  ·
                    refine ⟨5665607244253832434556813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777071496169221623037875 5665607244253832434556813)
                    ·
                      refine ⟨2124602716595187162958805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665607244253832434556813 2124602716595187162958805)
                      ·
                        rfl

theorem cell23_4137649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4137649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137649 prefixEnd_4137649 := by exact prefixLift 4137649
  have htrace : WordTrace (prefixWord ++ tailWord_4137649) baseStart_4137649 baseEnd_4137649 := by
    simpa [prefixWord, tailWord_4137649, baseEnd_4137649] using wordTrace_append hprefix tailTrace_4137649
  have hstable : (prefixWord ++ tailWord_4137649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137649).length < 2 ^ (prefixWord ++ tailWord_4137649).sum := by decide
  have hdescent : baseEnd_4137649 < baseStart_4137649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137672 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_4137672 : Nat := 118140960795 + 4137672 * 2 ^ 59
def prefixEnd_4137672 : Nat := 4983230072969 + 3 ^ 40 * 4137672 * 2
def baseEnd_4137672 : Nat := 2124614526650240572971199

theorem tailTrace_4137672 : CollatzResearch.WordTrace tailWord_4137672 prefixEnd_4137672 2124614526650240572971199 := by
  unfold tailWord_4137672
  simp only [CollatzResearch.WordTrace]
  refine ⟨75456647932964238481391635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100608863910618984641855513 75456647932964238481391635)
  ·
    refine ⟨113184971899446357722087453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75456647932964238481391635 113184971899446357722087453)
    ·
      refine ⟨42444364462292384145782795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113184971899446357722087453 42444364462292384145782795)
      ·
        refine ⟨63666546693438576218674193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42444364462292384145782795 63666546693438576218674193)
        ·
          refine ⟨47749910020078932164005645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63666546693438576218674193 47749910020078932164005645)
          ·
            refine ⟨17906216257529599561502117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47749910020078932164005645 17906216257529599561502117)
            ·
              refine ⟨3357415548286799917781647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17906216257529599561502117 3357415548286799917781647)
              ·
                refine ⟨5036123322430199876672471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357415548286799917781647 5036123322430199876672471)
                ·
                  refine ⟨7554184983645299815008707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036123322430199876672471 7554184983645299815008707)
                  ·
                    refine ⟨11331277475467949722513061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7554184983645299815008707 11331277475467949722513061)
                    ·
                      refine ⟨2124614526650240572971199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11331277475467949722513061 2124614526650240572971199)
                      ·
                        rfl

theorem cell23_4137672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_4137672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137672 prefixEnd_4137672 := by exact prefixLift 4137672
  have htrace : WordTrace (prefixWord ++ tailWord_4137672) baseStart_4137672 baseEnd_4137672 := by
    simpa [prefixWord, tailWord_4137672, baseEnd_4137672] using wordTrace_append hprefix tailTrace_4137672
  have hstable : (prefixWord ++ tailWord_4137672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137672).length < 2 ^ (prefixWord ++ tailWord_4137672).sum := by decide
  have hdescent : baseEnd_4137672 < baseStart_4137672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137678 : List Nat := [4, 1, 1, 1, 3, 3, 10]
def baseStart_4137678 : Nat := 118140960795 + 4137678 * 2 ^ 59
def prefixEnd_4137678 : Nat := 4983230072969 + 3 ^ 40 * 4137678 * 2
def baseEnd_4137678 : Nat := 26229847006594661104891

theorem tailTrace_4137678 : CollatzResearch.WordTrace tailWord_4137678 prefixEnd_4137678 26229847006594661104891 := by
  unfold tailWord_4137678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864189337988342498437711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100609009802604493325001125 18864189337988342498437711)
  ·
    refine ⟨28296284006982513747656567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18864189337988342498437711 28296284006982513747656567)
    ·
      refine ⟨42444426010473770621484851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28296284006982513747656567 42444426010473770621484851)
      ·
        refine ⟨63666639015710655932227277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42444426010473770621484851 63666639015710655932227277)
        ·
          refine ⟨23874989630891495974585229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63666639015710655932227277 23874989630891495974585229)
          ·
            refine ⟨8953121111584310990469461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23874989630891495974585229 8953121111584310990469461)
            ·
              refine ⟨26229847006594661104891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8953121111584310990469461 26229847006594661104891)
              ·
                rfl

theorem cell23_4137678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 10].length) (baseStart_4137678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137678 prefixEnd_4137678 := by exact prefixLift 4137678
  have htrace : WordTrace (prefixWord ++ tailWord_4137678) baseStart_4137678 baseEnd_4137678 := by
    simpa [prefixWord, tailWord_4137678, baseEnd_4137678] using wordTrace_append hprefix tailTrace_4137678
  have hstable : (prefixWord ++ tailWord_4137678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137678).length < 2 ^ (prefixWord ++ tailWord_4137678).sum := by decide
  have hdescent : baseEnd_4137678 < baseStart_4137678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137682 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_4137682 : Nat := 118140960795 + 4137682 * 2 ^ 59
def prefixEnd_4137682 : Nat := 4983230072969 + 3 ^ 40 * 4137682 * 2
def baseEnd_4137682 : Nat := 708206553818928511282051

theorem tailTrace_4137682 : CollatzResearch.WordTrace tailWord_4137682 prefixEnd_4137682 708206553818928511282051 := by
  unfold tailWord_4137682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37728415148973062167661825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100609107063928165780431533 37728415148973062167661825)
  ·
    refine ⟨28296311361729796625746369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37728415148973062167661825 28296311361729796625746369)
    ·
      refine ⟨21222233521297347469309777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28296311361729796625746369 21222233521297347469309777)
      ·
        refine ⟨15916675140973010601982333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21222233521297347469309777 15916675140973010601982333)
        ·
          refine ⟨5968753177864878975743375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15916675140973010601982333 5968753177864878975743375)
          ·
            refine ⟨8953129766797318463615063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968753177864878975743375 8953129766797318463615063)
            ·
              refine ⟨13429694650195977695422595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953129766797318463615063 13429694650195977695422595)
              ·
                refine ⟨20144541975293966543133893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429694650195977695422595 20144541975293966543133893)
                ·
                  refine ⟨3777101620367618726837605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20144541975293966543133893 3777101620367618726837605)
                  ·
                    refine ⟨708206553818928511282051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777101620367618726837605 708206553818928511282051)
                    ·
                      rfl

theorem cell23_4137682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_4137682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137682 prefixEnd_4137682 := by exact prefixLift 4137682
  have htrace : WordTrace (prefixWord ++ tailWord_4137682) baseStart_4137682 baseEnd_4137682 := by
    simpa [prefixWord, tailWord_4137682, baseEnd_4137682] using wordTrace_append hprefix tailTrace_4137682
  have hstable : (prefixWord ++ tailWord_4137682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137682).length < 2 ^ (prefixWord ++ tailWord_4137682).sum := by decide
  have hdescent : baseEnd_4137682 < baseStart_4137682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137689 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 1, 2, 2]
def baseStart_4137689 : Nat := 118140960795 + 4137689 * 2 ^ 59
def prefixEnd_4137689 : Nat := 4983230072969 + 3 ^ 40 * 4137689 * 2
def baseEnd_4137689 : Nat := 2124623255821367006458621

theorem tailTrace_4137689 : CollatzResearch.WordTrace tailWord_4137689 prefixEnd_4137689 2124623255821367006458621 := by
  unfold tailWord_4137689
  simp only [CollatzResearch.WordTrace]
  refine ⟨150913915906866888866152121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100609277271244592577434747 150913915906866888866152121)
  ·
    refine ⟨113185436930150166649614091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150913915906866888866152121 113185436930150166649614091)
    ·
      refine ⟨169778155395225249974421137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113185436930150166649614091 169778155395225249974421137)
      ·
        refine ⟨127333616546418937480815853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169778155395225249974421137 127333616546418937480815853)
        ·
          refine ⟨47750106204907101555305945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127333616546418937480815853 47750106204907101555305945)
          ·
            refine ⟨35812579653680326166479459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47750106204907101555305945 35812579653680326166479459)
            ·
              refine ⟨53718869480520489249719189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35812579653680326166479459 53718869480520489249719189)
              ·
                refine ⟨2518072006899397933580587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53718869480520489249719189 2518072006899397933580587)
                ·
                  refine ⟨3777108010349096900370881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518072006899397933580587 3777108010349096900370881)
                  ·
                    refine ⟨2832831007761822675278161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3777108010349096900370881 2832831007761822675278161)
                    ·
                      refine ⟨2124623255821367006458621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2832831007761822675278161 2124623255821367006458621)
                      ·
                        rfl

theorem cell23_4137689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_4137689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137689 prefixEnd_4137689 := by exact prefixLift 4137689
  have htrace : WordTrace (prefixWord ++ tailWord_4137689) baseStart_4137689 baseEnd_4137689 := by
    simpa [prefixWord, tailWord_4137689, baseEnd_4137689] using wordTrace_append hprefix tailTrace_4137689
  have hstable : (prefixWord ++ tailWord_4137689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137689).length < 2 ^ (prefixWord ++ tailWord_4137689).sum := by decide
  have hdescent : baseEnd_4137689 < baseStart_4137689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137692 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4137692 : Nat := 118140960795 + 4137692 * 2 ^ 59
def prefixEnd_4137692 : Nat := 4983230072969 + 3 ^ 40 * 4137692 * 2
def baseEnd_4137692 : Nat := 2124624796263330494721107

theorem tailTrace_4137692 : CollatzResearch.WordTrace tailWord_4137692 prefixEnd_4137692 2124624796263330494721107 := by
  unfold tailWord_4137692
  simp only [CollatzResearch.WordTrace]
  refine ⟨75457012662928010189255665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100609350217237346919007553 75457012662928010189255665)
  ·
    refine ⟨56592759497196007641941749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75457012662928010189255665 56592759497196007641941749)
    ·
      refine ⟨5305571202862125716432039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56592759497196007641941749 5305571202862125716432039)
      ·
        refine ⟨7958356804293188574648059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305571202862125716432039 7958356804293188574648059)
        ·
          refine ⟨11937535206439782861972089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958356804293188574648059 11937535206439782861972089)
          ·
            refine ⟨8953151404829837146479067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11937535206439782861972089 8953151404829837146479067)
            ·
              refine ⟨13429727107244755719718601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953151404829837146479067 13429727107244755719718601)
              ·
                refine ⟨10072295330433566789788951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13429727107244755719718601 10072295330433566789788951)
                ·
                  refine ⟨15108442995650350184683427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10072295330433566789788951 15108442995650350184683427)
                  ·
                    refine ⟨22662664493475525277025141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15108442995650350184683427 22662664493475525277025141)
                    ·
                      refine ⟨2124624796263330494721107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22662664493475525277025141 2124624796263330494721107)
                      ·
                        rfl

theorem cell23_4137692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4137692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137692 prefixEnd_4137692 := by exact prefixLift 4137692
  have htrace : WordTrace (prefixWord ++ tailWord_4137692) baseStart_4137692 baseEnd_4137692 := by
    simpa [prefixWord, tailWord_4137692, baseEnd_4137692] using wordTrace_append hprefix tailTrace_4137692
  have hstable : (prefixWord ++ tailWord_4137692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137692).length < 2 ^ (prefixWord ++ tailWord_4137692).sum := by decide
  have hdescent : baseEnd_4137692 < baseStart_4137692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137699 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 2, 4]
def baseStart_4137699 : Nat := 118140960795 + 4137699 * 2 ^ 59
def prefixEnd_4137699 : Nat := 4983230072969 + 3 ^ 40 * 4137699 * 2
def baseEnd_4137699 : Nat := 708209463542637322444525

theorem tailTrace_4137699 : CollatzResearch.WordTrace tailWord_4137699 prefixEnd_4137699 708209463542637322444525 := by
  unfold tailWord_4137699
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914280636830660574016151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100609520424553773716010767 150914280636830660574016151)
  ·
    refine ⟨226371420955245990861024227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150914280636830660574016151 226371420955245990861024227)
    ·
      refine ⟨339557131432868986291536341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226371420955245990861024227 339557131432868986291536341)
      ·
        refine ⟨7958370267957866866207883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 339557131432868986291536341 7958370267957866866207883)
        ·
          refine ⟨11937555401936800299311825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958370267957866866207883 11937555401936800299311825)
          ·
            refine ⟨8953166551452600224483869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11937555401936800299311825 8953166551452600224483869)
            ·
              refine ⟨3357437456794725084181451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8953166551452600224483869 3357437456794725084181451)
              ·
                refine ⟨5036156185192087626272177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357437456794725084181451 5036156185192087626272177)
                ·
                  refine ⟨3777117138894065719704133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036156185192087626272177 3777117138894065719704133)
                  ·
                    refine ⟨708209463542637322444525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777117138894065719704133 708209463542637322444525)
                    ·
                      rfl

theorem cell23_4137699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 4].length) (baseStart_4137699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137699 prefixEnd_4137699 := by exact prefixLift 4137699
  have htrace : WordTrace (prefixWord ++ tailWord_4137699) baseStart_4137699 baseEnd_4137699 := by
    simpa [prefixWord, tailWord_4137699, baseEnd_4137699] using wordTrace_append hprefix tailTrace_4137699
  have hstable : (prefixWord ++ tailWord_4137699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137699).length < 2 ^ (prefixWord ++ tailWord_4137699).sum := by decide
  have hdescent : baseEnd_4137699 < baseStart_4137699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137705 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_4137705 : Nat := 118140960795 + 4137705 * 2 ^ 59
def prefixEnd_4137705 : Nat := 4983230072969 + 3 ^ 40 * 4137705 * 2
def baseEnd_4137705 : Nat := 2124631471511838943858547

theorem tailTrace_4137705 : CollatzResearch.WordTrace tailWord_4137705 prefixEnd_4137705 2124631471511838943858547 := by
  unfold tailWord_4137705
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914499474808923598734569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100609666316539282399156379 150914499474808923598734569)
  ·
    refine ⟨113185874606106692699050927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150914499474808923598734569 113185874606106692699050927)
    ·
      refine ⟨169778811909160039048576391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113185874606106692699050927 169778811909160039048576391)
      ·
        refine ⟨254668217863740058572864587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169778811909160039048576391 254668217863740058572864587)
        ·
          refine ⟨382002326795610087859296881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254668217863740058572864587 382002326795610087859296881)
          ·
            refine ⟨286501745096707565894472661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382002326795610087859296881 286501745096707565894472661)
            ·
              refine ⟨6714884650704083575651703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 286501745096707565894472661 6714884650704083575651703)
              ·
                refine ⟨10072326976056125363477555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714884650704083575651703 10072326976056125363477555)
                ·
                  refine ⟨15108490464084188045216333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10072326976056125363477555 15108490464084188045216333)
                  ·
                    refine ⟨5665683924031570516956125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15108490464084188045216333 5665683924031570516956125)
                    ·
                      refine ⟨2124631471511838943858547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665683924031570516956125 2124631471511838943858547)
                      ·
                        rfl

theorem cell23_4137705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_4137705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137705 prefixEnd_4137705 := by exact prefixLift 4137705
  have htrace : WordTrace (prefixWord ++ tailWord_4137705) baseStart_4137705 baseEnd_4137705 := by
    simpa [prefixWord, tailWord_4137705, baseEnd_4137705] using wordTrace_append hprefix tailTrace_4137705
  have hstable : (prefixWord ++ tailWord_4137705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137705).length < 2 ^ (prefixWord ++ tailWord_4137705).sum := by decide
  have hdescent : baseEnd_4137705 < baseStart_4137705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137717 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4137717 : Nat := 118140960795 + 4137717 * 2 ^ 59
def prefixEnd_4137717 : Nat := 4983230072969 + 3 ^ 40 * 4137717 * 2
def baseEnd_4137717 : Nat := 2124637633279692896908493

theorem tailTrace_4137717 : CollatzResearch.WordTrace tailWord_4137717 prefixEnd_4137717 2124637633279692896908493 := by
  unfold tailWord_4137717
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914937150765449648171405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100609958100510299765447603 150914937150765449648171405)
  ·
    refine ⟨56593101431537043618064277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150914937150765449648171405 56593101431537043618064277)
    ·
      refine ⟨2652801629603298919596763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56593101431537043618064277 2652801629603298919596763)
      ·
        refine ⟨3979202444404948379395145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652801629603298919596763 3979202444404948379395145)
        ·
          refine ⟨2984401833303711284546359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979202444404948379395145 2984401833303711284546359)
          ·
            refine ⟨4476602749955566926819539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984401833303711284546359 4476602749955566926819539)
            ·
              refine ⟨6714904124933350390229309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476602749955566926819539 6714904124933350390229309)
              ·
                refine ⟨2518089046850006396335991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6714904124933350390229309 2518089046850006396335991)
                ·
                  refine ⟨3777133570275009594503987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518089046850006396335991 3777133570275009594503987)
                  ·
                    refine ⟨5665700355412514391755981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777133570275009594503987 5665700355412514391755981)
                    ·
                      refine ⟨2124637633279692896908493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665700355412514391755981 2124637633279692896908493)
                      ·
                        rfl

theorem cell23_4137717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4137717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137717 prefixEnd_4137717 := by exact prefixLift 4137717
  have htrace : WordTrace (prefixWord ++ tailWord_4137717) baseStart_4137717 baseEnd_4137717 := by
    simpa [prefixWord, tailWord_4137717, baseEnd_4137717] using wordTrace_append hprefix tailTrace_4137717
  have hstable : (prefixWord ++ tailWord_4137717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137717).length < 2 ^ (prefixWord ++ tailWord_4137717).sum := by decide
  have hdescent : baseEnd_4137717 < baseStart_4137717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137756 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_4137756 : Nat := 118140960795 + 4137756 * 2 ^ 59
def prefixEnd_4137756 : Nat := 4983230072969 + 3 ^ 40 * 4137756 * 2
def baseEnd_4137756 : Nat := 2124657659025218244320813

theorem tailTrace_4137756 : CollatzResearch.WordTrace tailWord_4137756 prefixEnd_4137756 2124657659025218244320813 := by
  unfold tailWord_4137756
  simp only [CollatzResearch.WordTrace]
  refine ⟨75458179798812079654420561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100610906398416106205894081 75458179798812079654420561)
  ·
    refine ⟨56593634849109059740815421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75458179798812079654420561 56593634849109059740815421)
    ·
      refine ⟨21222613068415897402805783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56593634849109059740815421 21222613068415897402805783)
      ·
        refine ⟨31833919602623846104208675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21222613068415897402805783 31833919602623846104208675)
        ·
          refine ⟨47750879403935769156313013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31833919602623846104208675 47750879403935769156313013)
          ·
            refine ⟨4476644944118978358404345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47750879403935769156313013 4476644944118978358404345)
            ·
              refine ⟨3357483708089233768803259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476644944118978358404345 3357483708089233768803259)
              ·
                refine ⟨5036225562133850653204889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357483708089233768803259 5036225562133850653204889)
                ·
                  refine ⟨3777169171600387989903667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036225562133850653204889 3777169171600387989903667)
                  ·
                    refine ⟨5665753757400581984855501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777169171600387989903667 5665753757400581984855501)
                    ·
                      refine ⟨2124657659025218244320813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665753757400581984855501 2124657659025218244320813)
                      ·
                        rfl

theorem cell23_4137756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_4137756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137756 prefixEnd_4137756 := by exact prefixLift 4137756
  have htrace : WordTrace (prefixWord ++ tailWord_4137756) baseStart_4137756 baseEnd_4137756 := by
    simpa [prefixWord, tailWord_4137756, baseEnd_4137756] using wordTrace_append hprefix tailTrace_4137756
  have hstable : (prefixWord ++ tailWord_4137756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137756).length < 2 ^ (prefixWord ++ tailWord_4137756).sum := by decide
  have hdescent : baseEnd_4137756 < baseStart_4137756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137795 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3]
def baseStart_4137795 : Nat := 118140960795 + 4137795 * 2 ^ 59
def prefixEnd_4137795 : Nat := 4983230072969 + 3 ^ 40 * 4137795 * 2
def baseEnd_4137795 : Nat := 2124677684770743591733133

theorem tailTrace_4137795 : CollatzResearch.WordTrace tailWord_4137795 prefixEnd_4137795 2124677684770743591733133 := by
  unfold tailWord_4137795
  simp only [CollatzResearch.WordTrace]
  refine ⟨150917782044482868969510839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100611854696321912646340559 150917782044482868969510839)
  ·
    refine ⟨226376673066724303454266259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150917782044482868969510839 226376673066724303454266259)
    ·
      refine ⟨339565009600086455181399389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226376673066724303454266259 339565009600086455181399389)
      ·
        refine ⟨127336878600032420693024771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339565009600086455181399389 127336878600032420693024771)
        ·
          refine ⟨191005317900048631039537157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127336878600032420693024771 191005317900048631039537157)
          ·
            refine ⟨35813497106259118319913217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191005317900048631039537157 35813497106259118319913217)
            ·
              refine ⟨26860122829694338739934913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35813497106259118319913217 26860122829694338739934913)
              ·
                refine ⟨20145092122270754054951185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26860122829694338739934913 20145092122270754054951185)
                ·
                  refine ⟨15108819091703065541213389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20145092122270754054951185 15108819091703065541213389)
                  ·
                    refine ⟨5665807159388649577955021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15108819091703065541213389 5665807159388649577955021)
                    ·
                      refine ⟨2124677684770743591733133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5665807159388649577955021 2124677684770743591733133)
                      ·
                        rfl

theorem cell23_4137795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_4137795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137795 prefixEnd_4137795 := by exact prefixLift 4137795
  have htrace : WordTrace (prefixWord ++ tailWord_4137795) baseStart_4137795 baseEnd_4137795 := by
    simpa [prefixWord, tailWord_4137795, baseEnd_4137795] using wordTrace_append hprefix tailTrace_4137795
  have hstable : (prefixWord ++ tailWord_4137795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137795).length < 2 ^ (prefixWord ++ tailWord_4137795).sum := by decide
  have hdescent : baseEnd_4137795 < baseStart_4137795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137832 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_4137832 : Nat := 118140960795 + 4137832 * 2 ^ 59
def prefixEnd_4137832 : Nat := 4983230072969 + 3 ^ 40 * 4137832 * 2
def baseEnd_4137832 : Nat := 708232227851653315656821

theorem tailTrace_4137832 : CollatzResearch.WordTrace tailWord_4137832 prefixEnd_4137832 708232227851653315656821 := by
  unfold tailWord_4137832
  simp only [CollatzResearch.WordTrace]
  refine ⟨75459565772674412144303875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100612754363565882859071833 75459565772674412144303875)
  ·
    refine ⟨113189348659011618216455813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75459565772674412144303875 113189348659011618216455813)
    ·
      refine ⟨21223002873564678415585465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113189348659011618216455813 21223002873564678415585465)
      ·
        refine ⟨15917252155173508811689099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21223002873564678415585465 15917252155173508811689099)
        ·
          refine ⟨23875878232760263217533649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15917252155173508811689099 23875878232760263217533649)
          ·
            refine ⟨17906908674570197413150237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23875878232760263217533649 17906908674570197413150237)
            ·
              refine ⟨6715090752963824029931339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17906908674570197413150237 6715090752963824029931339)
              ·
                refine ⟨10072636129445736044897009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715090752963824029931339 10072636129445736044897009)
                ·
                  refine ⟨7554477097084302033672757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072636129445736044897009 7554477097084302033672757)
                  ·
                    refine ⟨708232227851653315656821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7554477097084302033672757 708232227851653315656821)
                    ·
                      rfl

theorem cell23_4137832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_4137832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137832 prefixEnd_4137832 := by exact prefixLift 4137832
  have htrace : WordTrace (prefixWord ++ tailWord_4137832) baseStart_4137832 baseEnd_4137832 := by
    simpa [prefixWord, tailWord_4137832, baseEnd_4137832] using wordTrace_append hprefix tailTrace_4137832
  have hstable : (prefixWord ++ tailWord_4137832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137832).length < 2 ^ (prefixWord ++ tailWord_4137832).sum := by decide
  have hdescent : baseEnd_4137832 < baseStart_4137832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137946 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_4137946 : Nat := 118140960795 + 4137946 * 2 ^ 59
def prefixEnd_4137946 : Nat := 4983230072969 + 3 ^ 40 * 4137946 * 2
def baseEnd_4137946 : Nat := 2124755220349572500944939

theorem tailTrace_4137946 : CollatzResearch.WordTrace tailWord_4137946 prefixEnd_4137946 2124755220349572500944939 := by
  unfold tailWord_4137946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37730822366733955439564423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100615526311290547838838461 37730822366733955439564423)
  ·
    refine ⟨56596233550100933159346635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37730822366733955439564423 56596233550100933159346635)
    ·
      refine ⟨84894350325151399739019953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56596233550100933159346635 84894350325151399739019953)
      ·
        refine ⟨63670762743863549804264965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84894350325151399739019953 63670762743863549804264965)
        ·
          refine ⟨11938268014474415588299681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63670762743863549804264965 11938268014474415588299681)
          ·
            refine ⟨8953701010855811691224761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11938268014474415588299681 8953701010855811691224761)
            ·
              refine ⟨6715275758141858768418571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953701010855811691224761 6715275758141858768418571)
              ·
                refine ⟨10072913637212788152627857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715275758141858768418571 10072913637212788152627857)
                ·
                  refine ⟨7554685227909591114470893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072913637212788152627857 7554685227909591114470893)
                  ·
                    refine ⟨2833006960466096667926585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7554685227909591114470893 2833006960466096667926585)
                    ·
                      refine ⟨2124755220349572500944939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833006960466096667926585 2124755220349572500944939)
                      ·
                        rfl

theorem cell23_4137946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_4137946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137946 prefixEnd_4137946 := by exact prefixLift 4137946
  have htrace : WordTrace (prefixWord ++ tailWord_4137946) baseStart_4137946 baseEnd_4137946 := by
    simpa [prefixWord, tailWord_4137946, baseEnd_4137946] using wordTrace_append hprefix tailTrace_4137946
  have hstable : (prefixWord ++ tailWord_4137946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137946).length < 2 ^ (prefixWord ++ tailWord_4137946).sum := by decide
  have hdescent : baseEnd_4137946 < baseStart_4137946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137965 : List Nat := [1, 5, 1, 16]
def baseStart_4137965 : Nat := 118140960795 + 4137965 * 2 ^ 59
def prefixEnd_4137965 : Nat := 4983230072969 + 3 ^ 40 * 4137965 * 2
def baseEnd_4137965 : Nat := 971543199123003167173

theorem tailTrace_4137965 : CollatzResearch.WordTrace tailWord_4137965 prefixEnd_4137965 971543199123003167173 := by
  unfold tailWord_4137965
  simp only [CollatzResearch.WordTrace]
  refine ⟨150923982453866988003199349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100615988302577992002132899 150923982453866988003199349)
  ·
    refine ⟨14149123355050030125299939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150923982453866988003199349 14149123355050030125299939)
    ·
      refine ⟨21223685032575045187949909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149123355050030125299939 21223685032575045187949909)
      ·
        refine ⟨971543199123003167173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 21223685032575045187949909 971543199123003167173)
        ·
          rfl

theorem cell23_4137965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 16].length) (baseStart_4137965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137965 prefixEnd_4137965 := by exact prefixLift 4137965
  have htrace : WordTrace (prefixWord ++ tailWord_4137965) baseStart_4137965 baseEnd_4137965 := by
    simpa [prefixWord, tailWord_4137965, baseEnd_4137965] using wordTrace_append hprefix tailTrace_4137965
  have hstable : (prefixWord ++ tailWord_4137965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137965).length < 2 ^ (prefixWord ++ tailWord_4137965).sum := by decide
  have hdescent : baseEnd_4137965 < baseStart_4137965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137969 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_4137969 : Nat := 118140960795 + 4137969 * 2 ^ 59
def prefixEnd_4137969 : Nat := 4983230072969 + 3 ^ 40 * 4137969 * 2
def baseEnd_4137969 : Nat := 708255676801541970319111

theorem tailTrace_4137969 : CollatzResearch.WordTrace tailWord_4137969 prefixEnd_4137969 708255676801541970319111 := by
  unfold tailWord_4137969
  simp only [CollatzResearch.WordTrace]
  refine ⟨150924128345852496686344961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100616085563901664457563307 150924128345852496686344961)
  ·
    refine ⟨113193096259389372514758721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150924128345852496686344961 113193096259389372514758721)
    ·
      refine ⟨84894822194542029386069041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113193096259389372514758721 84894822194542029386069041)
      ·
        refine ⟨63671116645906522039551781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84894822194542029386069041 63671116645906522039551781)
        ·
          refine ⟨11938334371107472882415959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63671116645906522039551781 11938334371107472882415959)
          ·
            refine ⟨17907501556661209323623939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938334371107472882415959 17907501556661209323623939)
            ·
              refine ⟨26861252334991813985435909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907501556661209323623939 26861252334991813985435909)
              ·
                refine ⟨5036484812810965122269233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26861252334991813985435909 5036484812810965122269233)
                ·
                  refine ⟨3777363609608223841701925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036484812810965122269233 3777363609608223841701925)
                  ·
                    refine ⟨708255676801541970319111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777363609608223841701925 708255676801541970319111)
                    ·
                      rfl

theorem cell23_4137969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_4137969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137969 prefixEnd_4137969 := by exact prefixLift 4137969
  have htrace : WordTrace (prefixWord ++ tailWord_4137969) baseStart_4137969 baseEnd_4137969 := by
    simpa [prefixWord, tailWord_4137969, baseEnd_4137969] using wordTrace_append hprefix tailTrace_4137969
  have hstable : (prefixWord ++ tailWord_4137969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137969).length < 2 ^ (prefixWord ++ tailWord_4137969).sum := by decide
  have hdescent : baseEnd_4137969 < baseStart_4137969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137970 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4137970 : Nat := 118140960795 + 4137970 * 2 ^ 59
def prefixEnd_4137970 : Nat := 4983230072969 + 3 ^ 40 * 4137970 * 2
def baseEnd_4137970 : Nat := 2124767543885280407044829

theorem tailTrace_4137970 : CollatzResearch.WordTrace tailWord_4137970 prefixEnd_4137970 2124767543885280407044829 := by
  unfold tailWord_4137970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37731041204712218464282841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100616109879232582571420909 37731041204712218464282841)
  ·
    refine ⟨28298280903534163848212131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37731041204712218464282841 28298280903534163848212131)
    ·
      refine ⟨42447421355301245772318197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28298280903534163848212131 42447421355301245772318197)
      ·
        refine ⟨3979445752059491791154831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42447421355301245772318197 3979445752059491791154831)
        ·
          refine ⟨5969168628089237686732247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979445752059491791154831 5969168628089237686732247)
          ·
            refine ⟨8953752942133856530098371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969168628089237686732247 8953752942133856530098371)
            ·
              refine ⟨13430629413200784795147557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953752942133856530098371 13430629413200784795147557)
              ·
                refine ⟨2518243014975147149090167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13430629413200784795147557 2518243014975147149090167)
                ·
                  refine ⟨3777364522462720723635251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518243014975147149090167 3777364522462720723635251)
                  ·
                    refine ⟨5666046783694081085452877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777364522462720723635251 5666046783694081085452877)
                    ·
                      refine ⟨2124767543885280407044829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666046783694081085452877 2124767543885280407044829)
                      ·
                        rfl

theorem cell23_4137970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4137970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4137970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4137970 prefixEnd_4137970 := by exact prefixLift 4137970
  have htrace : WordTrace (prefixWord ++ tailWord_4137970) baseStart_4137970 baseEnd_4137970 := by
    simpa [prefixWord, tailWord_4137970, baseEnd_4137970] using wordTrace_append hprefix tailTrace_4137970
  have hstable : (prefixWord ++ tailWord_4137970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137970).length < 2 ^ (prefixWord ++ tailWord_4137970).sum := by decide
  have hdescent : baseEnd_4137970 < baseStart_4137970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138025 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_4138025 : Nat := 118140960795 + 4138025 * 2 ^ 59
def prefixEnd_4138025 : Nat := 4983230072969 + 3 ^ 40 * 4138025 * 2
def baseEnd_4138025 : Nat := 708265261773759230619025

theorem tailTrace_4138025 : CollatzResearch.WordTrace tailWord_4138025 prefixEnd_4138025 708265261773759230619025 := by
  unfold tailWord_4138025
  simp only [CollatzResearch.WordTrace]
  refine ⟨150926170833649618250383529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100617447222433078833589019 150926170833649618250383529)
  ·
    refine ⟨113194628125237213687787647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150926170833649618250383529 113194628125237213687787647)
    ·
      refine ⟨169791942187855820531681471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113194628125237213687787647 169791942187855820531681471)
      ·
        refine ⟨254687913281783730797522207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169791942187855820531681471 254687913281783730797522207)
        ·
          refine ⟨382031869922675596196283311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254687913281783730797522207 382031869922675596196283311)
          ·
            refine ⟨573047804884013394294424967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382031869922675596196283311 573047804884013394294424967)
            ·
              refine ⟨859571707326020091441637451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573047804884013394294424967 859571707326020091441637451)
              ·
                refine ⟨1289357560989030137162456177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859571707326020091441637451 1289357560989030137162456177)
                ·
                  refine ⟨967018170741772602871842133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289357560989030137162456177 967018170741772602871842133)
                  ·
                    refine ⟨708265261773759230619025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 967018170741772602871842133 708265261773759230619025)
                    ·
                      rfl

theorem cell23_4138025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_4138025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138025 prefixEnd_4138025 := by exact prefixLift 4138025
  have htrace : WordTrace (prefixWord ++ tailWord_4138025) baseStart_4138025 baseEnd_4138025 := by
    simpa [prefixWord, tailWord_4138025, baseEnd_4138025] using wordTrace_append hprefix tailTrace_4138025
  have hstable : (prefixWord ++ tailWord_4138025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138025).length < 2 ^ (prefixWord ++ tailWord_4138025).sum := by decide
  have hdescent : baseEnd_4138025 < baseStart_4138025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138042 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_4138042 : Nat := 118140960795 + 4138042 * 2 ^ 59
def prefixEnd_4138042 : Nat := 4983230072969 + 3 ^ 40 * 4138042 * 2
def baseEnd_4138042 : Nat := 708268171497468041781499

theorem tailTrace_4138042 : CollatzResearch.WordTrace tailWord_4138042 prefixEnd_4138042 708268171497468041781499 := by
  unfold tailWord_4138042
  simp only [CollatzResearch.WordTrace]
  refine ⟨37731697718647007538438095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100617860583058686769168253 37731697718647007538438095)
  ·
    refine ⟨56597546577970511307657143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37731697718647007538438095 56597546577970511307657143)
    ·
      refine ⟨84896319866955766961485715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56597546577970511307657143 84896319866955766961485715)
      ·
        refine ⟨127344479800433650442228573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84896319866955766961485715 127344479800433650442228573)
        ·
          refine ⟨47754179925162618915835715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127344479800433650442228573 47754179925162618915835715)
          ·
            refine ⟨71631269887743928373753573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47754179925162618915835715 71631269887743928373753573)
            ·
              refine ⟨13430863103951986570078795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71631269887743928373753573 13430863103951986570078795)
              ·
                refine ⟨20146294655927979855118193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13430863103951986570078795 20146294655927979855118193)
                ·
                  refine ⟨15109720991945984891338645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20146294655927979855118193 15109720991945984891338645)
                  ·
                    refine ⟨708268171497468041781499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15109720991945984891338645 708268171497468041781499)
                    ·
                      rfl

theorem cell23_4138042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_4138042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138042 prefixEnd_4138042 := by exact prefixLift 4138042
  have htrace : WordTrace (prefixWord ++ tailWord_4138042) baseStart_4138042 baseEnd_4138042 := by
    simpa [prefixWord, tailWord_4138042, baseEnd_4138042] using wordTrace_append hprefix tailTrace_4138042
  have hstable : (prefixWord ++ tailWord_4138042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138042).length < 2 ^ (prefixWord ++ tailWord_4138042).sum := by decide
  have hdescent : baseEnd_4138042 < baseStart_4138042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138089 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 7]
def baseStart_4138089 : Nat := 118140960795 + 4138089 * 2 ^ 59
def prefixEnd_4138089 : Nat := 4983230072969 + 3 ^ 40 * 4138089 * 2
def baseEnd_4138089 : Nat := 236092072009240604606309

theorem tailTrace_4138089 : CollatzResearch.WordTrace tailWord_4138089 prefixEnd_4138089 236092072009240604606309 := by
  unfold tailWord_4138089
  simp only [CollatzResearch.WordTrace]
  refine ⟨150928505105417757180713321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100619003403611838120475547 150928505105417757180713321)
  ·
    refine ⟨113196378829063317885534991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150928505105417757180713321 113196378829063317885534991)
    ·
      refine ⟨169794568243594976828302487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113196378829063317885534991 169794568243594976828302487)
      ·
        refine ⟨254691852365392465242453731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169794568243594976828302487 254691852365392465242453731)
        ·
          refine ⟨382037778548088697863680597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254691852365392465242453731 382037778548088697863680597)
          ·
            refine ⟨4477005217360414428090007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 382037778548088697863680597 4477005217360414428090007)
            ·
              refine ⟨6715507826040621642135011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477005217360414428090007 6715507826040621642135011)
              ·
                refine ⟨10073261739060932463202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715507826040621642135011 10073261739060932463202517)
                ·
                  refine ⟨236092072009240604606309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10073261739060932463202517 236092072009240604606309)
                  ·
                    rfl

theorem cell23_4138089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_4138089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138089 prefixEnd_4138089 := by exact prefixLift 4138089
  have htrace : WordTrace (prefixWord ++ tailWord_4138089) baseStart_4138089 baseEnd_4138089 := by
    simpa [prefixWord, tailWord_4138089, baseEnd_4138089] using wordTrace_append hprefix tailTrace_4138089
  have hstable : (prefixWord ++ tailWord_4138089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138089).length < 2 ^ (prefixWord ++ tailWord_4138089).sum := by decide
  have hdescent : baseEnd_4138089 < baseStart_4138089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138159 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_4138159 : Nat := 118140960795 + 4138159 * 2 ^ 59
def prefixEnd_4138159 : Nat := 4983230072969 + 3 ^ 40 * 4138159 * 2
def baseEnd_4138159 : Nat := 2124864591728980167581459

theorem tailTrace_4138159 : CollatzResearch.WordTrace tailWord_4138159 prefixEnd_4138159 2124864591728980167581459 := by
  unfold tailWord_4138159
  simp only [CollatzResearch.WordTrace]
  refine ⟨150931058215164159135761531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100620705476776106090507687 150931058215164159135761531)
  ·
    refine ⟨226396587322746238703642297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150931058215164159135761531 226396587322746238703642297)
    ·
      refine ⟨169797440492059679027731723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226396587322746238703642297 169797440492059679027731723)
      ·
        refine ⟨254696160738089518541597585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169797440492059679027731723 254696160738089518541597585)
        ·
          refine ⟨191022120553567138906198189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254696160738089518541597585 191022120553567138906198189)
          ·
            refine ⟨71633295207587677089824321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191022120553567138906198189 71633295207587677089824321)
            ·
              refine ⟨53724971405690757817368241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71633295207587677089824321 53724971405690757817368241)
              ·
                refine ⟨40293728554268068363026181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53724971405690757817368241 40293728554268068363026181)
                ·
                  refine ⟨7555074103925262818067409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40293728554268068363026181 7555074103925262818067409)
                  ·
                    refine ⟨5666305577943947113550557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555074103925262818067409 5666305577943947113550557)
                    ·
                      refine ⟨2124864591728980167581459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666305577943947113550557 2124864591728980167581459)
                      ·
                        rfl

theorem cell23_4138159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_4138159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138159 prefixEnd_4138159 := by exact prefixLift 4138159
  have htrace : WordTrace (prefixWord ++ tailWord_4138159) baseStart_4138159 baseEnd_4138159 := by
    simpa [prefixWord, tailWord_4138159, baseEnd_4138159] using wordTrace_append hprefix tailTrace_4138159
  have hstable : (prefixWord ++ tailWord_4138159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138159).length < 2 ^ (prefixWord ++ tailWord_4138159).sum := by decide
  have hdescent : baseEnd_4138159 < baseStart_4138159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138176 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_4138176 : Nat := 118140960795 + 4138176 * 2 ^ 59
def prefixEnd_4138176 : Nat := 4983230072969 + 3 ^ 40 * 4138176 * 2
def baseEnd_4138176 : Nat := 2124873320900106601068881

theorem tailTrace_4138176 : CollatzResearch.WordTrace tailWord_4138176 prefixEnd_4138176 2124873320900106601068881 := by
  unfold tailWord_4138176
  simp only [CollatzResearch.WordTrace]
  refine ⟨75465839128051285519565191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100621118837401714026086921 75465839128051285519565191)
  ·
    refine ⟨113198758692076928279347787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75465839128051285519565191 113198758692076928279347787)
    ·
      refine ⟨169798138038115392419021681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113198758692076928279347787 169798138038115392419021681)
      ·
        refine ⟨127348603528586544314266261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169798138038115392419021681 127348603528586544314266261)
        ·
          refine ⟨5969465790402494264731231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127348603528586544314266261 5969465790402494264731231)
          ·
            refine ⟨8954198685603741397096847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969465790402494264731231 8954198685603741397096847)
            ·
              refine ⟨13431298028405612095645271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954198685603741397096847 13431298028405612095645271)
              ·
                refine ⟨20146947042608418143467907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13431298028405612095645271 20146947042608418143467907)
                ·
                  refine ⟨30220420563912627215201861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20146947042608418143467907 30220420563912627215201861)
                  ·
                    refine ⟨5666328855733617602850349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30220420563912627215201861 5666328855733617602850349)
                    ·
                      refine ⟨2124873320900106601068881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666328855733617602850349 2124873320900106601068881)
                      ·
                        rfl

theorem cell23_4138176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_4138176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138176 prefixEnd_4138176 := by exact prefixLift 4138176
  have htrace : WordTrace (prefixWord ++ tailWord_4138176) baseStart_4138176 baseEnd_4138176 := by
    simpa [prefixWord, tailWord_4138176, baseEnd_4138176] using wordTrace_append hprefix tailTrace_4138176
  have hstable : (prefixWord ++ tailWord_4138176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138176).length < 2 ^ (prefixWord ++ tailWord_4138176).sum := by decide
  have hdescent : baseEnd_4138176 < baseStart_4138176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138213 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 6]
def baseStart_4138213 : Nat := 118140960795 + 4138213 * 2 ^ 59
def prefixEnd_4138213 : Nat := 4983230072969 + 3 ^ 40 * 4138213 * 2
def baseEnd_4138213 : Nat := 236099146631591439589579

theorem tailTrace_4138213 : CollatzResearch.WordTrace tailWord_4138213 prefixEnd_4138213 236099146631591439589579 := by
  unfold tailWord_4138213
  simp only [CollatzResearch.WordTrace]
  refine ⟨150933027756968526358227293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100622018504645684238818195 150933027756968526358227293)
  ·
    refine ⟨56599885408863197384335235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150933027756968526358227293 56599885408863197384335235)
    ·
      refine ⟨84899828113294796076502853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56599885408863197384335235 84899828113294796076502853)
      ·
        refine ⟨15918717771242774264344285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84899828113294796076502853 15918717771242774264344285)
        ·
          refine ⟨5969519164216040349129107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15918717771242774264344285 5969519164216040349129107)
          ·
            refine ⟨8954278746324060523693661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969519164216040349129107 8954278746324060523693661)
            ·
              refine ⟨3357854529871522696385123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8954278746324060523693661 3357854529871522696385123)
              ·
                refine ⟨5036781794807284044577685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357854529871522696385123 5036781794807284044577685)
                ·
                  refine ⟨236099146631591439589579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5036781794807284044577685 236099146631591439589579)
                  ·
                    rfl

theorem cell23_4138213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_4138213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138213 prefixEnd_4138213 := by exact prefixLift 4138213
  have htrace : WordTrace (prefixWord ++ tailWord_4138213) baseStart_4138213 baseEnd_4138213 := by
    simpa [prefixWord, tailWord_4138213, baseEnd_4138213] using wordTrace_append hprefix tailTrace_4138213
  have hstable : (prefixWord ++ tailWord_4138213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138213).length < 2 ^ (prefixWord ++ tailWord_4138213).sum := by decide
  have hdescent : baseEnd_4138213 < baseStart_4138213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138216 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4138216 : Nat := 118140960795 + 4138216 * 2 ^ 59
def prefixEnd_4138216 : Nat := 4983230072969 + 3 ^ 40 * 4138216 * 2
def baseEnd_4138216 : Nat := 2124893860126286444568697

theorem tailTrace_4138216 : CollatzResearch.WordTrace tailWord_4138216 prefixEnd_4138216 2124893860126286444568697 := by
  unfold tailWord_4138216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75466568587978828935293251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100622091450638438580391001 75466568587978828935293251)
  ·
    refine ⟨113199852881968243402939877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75466568587978828935293251 113199852881968243402939877)
    ·
      refine ⟨21224972415369045638051227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113199852881968243402939877 21224972415369045638051227)
      ·
        refine ⟨31837458623053568457076841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21224972415369045638051227 31837458623053568457076841)
        ·
          refine ⟨23878093967290176342807631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31837458623053568457076841 23878093967290176342807631)
          ·
            refine ⟨35817140950935264514211447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23878093967290176342807631 35817140950935264514211447)
            ·
              refine ⟨53725711426402896771317171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35817140950935264514211447 53725711426402896771317171)
              ·
                refine ⟨80588567139604345156975757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53725711426402896771317171 80588567139604345156975757)
                ·
                  refine ⟨30220712677351629433865909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80588567139604345156975757 30220712677351629433865909)
                  ·
                    refine ⟨2833191813501715259424929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30220712677351629433865909 2833191813501715259424929)
                    ·
                      refine ⟨2124893860126286444568697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833191813501715259424929 2124893860126286444568697)
                      ·
                        rfl

theorem cell23_4138216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4138216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138216 prefixEnd_4138216 := by exact prefixLift 4138216
  have htrace : WordTrace (prefixWord ++ tailWord_4138216) baseStart_4138216 baseEnd_4138216 := by
    simpa [prefixWord, tailWord_4138216, baseEnd_4138216] using wordTrace_append hprefix tailTrace_4138216
  have hstable : (prefixWord ++ tailWord_4138216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138216).length < 2 ^ (prefixWord ++ tailWord_4138216).sum := by decide
  have hdescent : baseEnd_4138216 < baseStart_4138216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138266 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_4138266 : Nat := 118140960795 + 4138266 * 2 ^ 59
def prefixEnd_4138266 : Nat := 4983230072969 + 3 ^ 40 * 4138266 * 2
def baseEnd_4138266 : Nat := 2124919534159011248943467

theorem tailTrace_4138266 : CollatzResearch.WordTrace tailWord_4138266 prefixEnd_4138266 2124919534159011248943467 := by
  unfold tailWord_4138266
  simp only [CollatzResearch.WordTrace]
  refine ⟨37733740206444129102476663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100623307217184344273271101 37733740206444129102476663)
  ·
    refine ⟨56600610309666193653714995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37733740206444129102476663 56600610309666193653714995)
    ·
      refine ⟨84900915464499290480572493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56600610309666193653714995 84900915464499290480572493)
      ·
        refine ⟨31837843299187233930214685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84900915464499290480572493 31837843299187233930214685)
        ·
          refine ⟨11939191237195212723830507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31837843299187233930214685 11939191237195212723830507)
          ·
            refine ⟨17908786855792819085745761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11939191237195212723830507 17908786855792819085745761)
            ·
              refine ⟨13431590141844614314309321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17908786855792819085745761 13431590141844614314309321)
              ·
                refine ⟨10073692606383460735731991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13431590141844614314309321 10073692606383460735731991)
                ·
                  refine ⟨15110538909575191103597987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073692606383460735731991 15110538909575191103597987)
                  ·
                    refine ⟨22665808364362786655396981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15110538909575191103597987 22665808364362786655396981)
                    ·
                      refine ⟨2124919534159011248943467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22665808364362786655396981 2124919534159011248943467)
                      ·
                        rfl

theorem cell23_4138266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_4138266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138266 prefixEnd_4138266 := by exact prefixLift 4138266
  have htrace : WordTrace (prefixWord ++ tailWord_4138266) baseStart_4138266 baseEnd_4138266 := by
    simpa [prefixWord, tailWord_4138266, baseEnd_4138266] using wordTrace_append hprefix tailTrace_4138266
  have hstable : (prefixWord ++ tailWord_4138266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138266).length < 2 ^ (prefixWord ++ tailWord_4138266).sum := by decide
  have hdescent : baseEnd_4138266 < baseStart_4138266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138276 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4138276 : Nat := 118140960795 + 4138276 * 2 ^ 59
def prefixEnd_4138276 : Nat := 4983230072969 + 3 ^ 40 * 4138276 * 2
def baseEnd_4138276 : Nat := 2124924668965556209818421

theorem tailTrace_4138276 : CollatzResearch.WordTrace tailWord_4138276 prefixEnd_4138276 2124924668965556209818421 := by
  unfold tailWord_4138276
  simp only [CollatzResearch.WordTrace]
  refine ⟨75467662777870144058885341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100623550370493525411847121 75467662777870144058885341)
  ·
    refine ⟨28300373541701304022082003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75467662777870144058885341 28300373541701304022082003)
    ·
      refine ⟨42450560312551956033123005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28300373541701304022082003 42450560312551956033123005)
      ·
        refine ⟨15918960117206983512421127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42450560312551956033123005 15918960117206983512421127)
        ·
          refine ⟨23878440175810475268631691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918960117206983512421127 23878440175810475268631691)
          ·
            refine ⟨35817660263715712902947537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23878440175810475268631691 35817660263715712902947537)
            ·
              refine ⟨26863245197786784677210653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35817660263715712902947537 26863245197786784677210653)
              ·
                refine ⟨10073716949170044253953995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26863245197786784677210653 10073716949170044253953995)
                ·
                  refine ⟨15110575423755066380930993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073716949170044253953995 15110575423755066380930993)
                  ·
                    refine ⟨11332931567816299785698245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15110575423755066380930993 11332931567816299785698245)
                    ·
                      refine ⟨2124924668965556209818421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11332931567816299785698245 2124924668965556209818421)
                      ·
                        rfl

theorem cell23_4138276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4138276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138276 prefixEnd_4138276 := by exact prefixLift 4138276
  have htrace : WordTrace (prefixWord ++ tailWord_4138276) baseStart_4138276 baseEnd_4138276 := by
    simpa [prefixWord, tailWord_4138276, baseEnd_4138276] using wordTrace_append hprefix tailTrace_4138276
  have hstable : (prefixWord ++ tailWord_4138276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138276).length < 2 ^ (prefixWord ++ tailWord_4138276).sum := by decide
  have hdescent : baseEnd_4138276 < baseStart_4138276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138280 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4138280 : Nat := 118140960795 + 4138280 * 2 ^ 59
def prefixEnd_4138280 : Nat := 4983230072969 + 3 ^ 40 * 4138280 * 2
def baseEnd_4138280 : Nat := 2124926722888174194168403

theorem tailTrace_4138280 : CollatzResearch.WordTrace tailWord_4138280 prefixEnd_4138280 2124926722888174194168403 := by
  unfold tailWord_4138280
  simp only [CollatzResearch.WordTrace]
  refine ⟨75467735723862898400458147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100623647631817197867277529 75467735723862898400458147)
  ·
    refine ⟨113201603585794347600687221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75467735723862898400458147 113201603585794347600687221)
    ·
      refine ⟨10612650336168220087564427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113201603585794347600687221 10612650336168220087564427)
      ·
        refine ⟨15918975504252330131346641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612650336168220087564427 15918975504252330131346641)
        ·
          refine ⟨11939231628189247598509981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15918975504252330131346641 11939231628189247598509981)
          ·
            refine ⟨4477211860570967849441243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11939231628189247598509981 4477211860570967849441243)
            ·
              refine ⟨6715817790856451774161865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477211860570967849441243 6715817790856451774161865)
              ·
                refine ⟨5036863343142338830621399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6715817790856451774161865 5036863343142338830621399)
                ·
                  refine ⟨7555295014713508245932099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036863343142338830621399 7555295014713508245932099)
                  ·
                    refine ⟨11332942522070262368898149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555295014713508245932099 11332942522070262368898149)
                    ·
                      refine ⟨2124926722888174194168403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11332942522070262368898149 2124926722888174194168403)
                      ·
                        rfl

theorem cell23_4138280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4138280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138280 prefixEnd_4138280 := by exact prefixLift 4138280
  have htrace : WordTrace (prefixWord ++ tailWord_4138280) baseStart_4138280 baseEnd_4138280 := by
    simpa [prefixWord, tailWord_4138280, baseEnd_4138280] using wordTrace_append hprefix tailTrace_4138280
  have hstable : (prefixWord ++ tailWord_4138280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138280).length < 2 ^ (prefixWord ++ tailWord_4138280).sum := by decide
  have hdescent : baseEnd_4138280 < baseStart_4138280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138300 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_4138300 : Nat := 118140960795 + 4138300 * 2 ^ 59
def prefixEnd_4138300 : Nat := 4983230072969 + 3 ^ 40 * 4138300 * 2
def baseEnd_4138300 : Nat := 2124936992501264115918311

theorem tailTrace_4138300 : CollatzResearch.WordTrace tailWord_4138300 prefixEnd_4138300 2124936992501264115918311 := by
  unfold tailWord_4138300
  simp only [CollatzResearch.WordTrace]
  refine ⟨75468100453826670108322177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100624133938435560144429569 75468100453826670108322177)
  ·
    refine ⟨56601075340370002581241633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75468100453826670108322177 56601075340370002581241633)
    ·
      refine ⟨42450806505277501935931225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56601075340370002581241633 42450806505277501935931225)
      ·
        refine ⟨31838104878958126451948419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42450806505277501935931225 31838104878958126451948419)
        ·
          refine ⟨47757157318437189677922629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31838104878958126451948419 47757157318437189677922629)
          ·
            refine ⟨8954466997206973064610493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47757157318437189677922629 8954466997206973064610493)
            ·
              refine ⟨3357925123952614899228935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8954466997206973064610493 3357925123952614899228935)
              ·
                refine ⟨5036887685928922348843403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357925123952614899228935 5036887685928922348843403)
                ·
                  refine ⟨7555331528893383523265105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036887685928922348843403 7555331528893383523265105)
                  ·
                    refine ⟨5666498646670037642448829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555331528893383523265105 5666498646670037642448829)
                    ·
                      refine ⟨2124936992501264115918311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666498646670037642448829 2124936992501264115918311)
                      ·
                        rfl

theorem cell23_4138300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_4138300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138300 prefixEnd_4138300 := by exact prefixLift 4138300
  have htrace : WordTrace (prefixWord ++ tailWord_4138300) baseStart_4138300 baseEnd_4138300 := by
    simpa [prefixWord, tailWord_4138300, baseEnd_4138300] using wordTrace_append hprefix tailTrace_4138300
  have hstable : (prefixWord ++ tailWord_4138300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138300).length < 2 ^ (prefixWord ++ tailWord_4138300).sum := by decide
  have hdescent : baseEnd_4138300 < baseStart_4138300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138309 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_4138309 : Nat := 118140960795 + 4138309 * 2 ^ 59
def prefixEnd_4138309 : Nat := 4983230072969 + 3 ^ 40 * 4138309 * 2
def baseEnd_4138309 : Nat := 2124941613827154580705769

theorem tailTrace_4138309 : CollatzResearch.WordTrace tailWord_4138309 prefixEnd_4138309 2124941613827154580705769 := by
  unfold tailWord_4138309
  simp only [CollatzResearch.WordTrace]
  refine ⟨150936529164620734753721981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100624352776413823169147987 150936529164620734753721981)
  ·
    refine ⟨56601198436732775532645743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150936529164620734753721981 56601198436732775532645743)
    ·
      refine ⟨84901797655099163298968615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56601198436732775532645743 84901797655099163298968615)
      ·
        refine ⟨127352696482648744948452923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84901797655099163298968615 127352696482648744948452923)
        ·
          refine ⟨191029044723973117422679385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127352696482648744948452923 191029044723973117422679385)
          ·
            refine ⟨143271783542979838067009539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191029044723973117422679385 143271783542979838067009539)
            ·
              refine ⟨214907675314469757100514309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143271783542979838067009539 214907675314469757100514309)
              ·
                refine ⟨40295189121463079456346433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214907675314469757100514309 40295189121463079456346433)
                ·
                  refine ⟨30221391841097309592259825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40295189121463079456346433 30221391841097309592259825)
                  ·
                    refine ⟨22666043880822982194194869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30221391841097309592259825 22666043880822982194194869)
                    ·
                      refine ⟨2124941613827154580705769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22666043880822982194194869 2124941613827154580705769)
                      ·
                        rfl

theorem cell23_4138309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_4138309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138309 prefixEnd_4138309 := by exact prefixLift 4138309
  have htrace : WordTrace (prefixWord ++ tailWord_4138309) baseStart_4138309 baseEnd_4138309 := by
    simpa [prefixWord, tailWord_4138309, baseEnd_4138309] using wordTrace_append hprefix tailTrace_4138309
  have hstable : (prefixWord ++ tailWord_4138309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138309).length < 2 ^ (prefixWord ++ tailWord_4138309).sum := by decide
  have hdescent : baseEnd_4138309 < baseStart_4138309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138313 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 3]
def baseStart_4138313 : Nat := 118140960795 + 4138313 * 2 ^ 59
def prefixEnd_4138313 : Nat := 4983230072969 + 3 ^ 40 * 4138313 * 2
def baseEnd_4138313 : Nat := 2124943667749772565055751

theorem tailTrace_4138313 : CollatzResearch.WordTrace tailWord_4138313 prefixEnd_4138313 2124943667749772565055751 := by
  unfold tailWord_4138313
  simp only [CollatzResearch.WordTrace]
  refine ⟨150936675056606243436867593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100624450037737495624578395 150936675056606243436867593)
  ·
    refine ⟨113202506292454682577650695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150936675056606243436867593 113202506292454682577650695)
    ·
      refine ⟨169803759438682023866476043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113202506292454682577650695 169803759438682023866476043)
      ·
        refine ⟨254705639158023035799714065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169803759438682023866476043 254705639158023035799714065)
        ·
          refine ⟨191029229368517276849785549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254705639158023035799714065 191029229368517276849785549)
          ·
            refine ⟨71635961013193978818669581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191029229368517276849785549 71635961013193978818669581)
            ·
              refine ⟨26863485379947742057001093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71635961013193978818669581 26863485379947742057001093)
              ·
                refine ⟨5036903508740201635687705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26863485379947742057001093 5036903508740201635687705)
                ·
                  refine ⟨3777677631555151226765779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036903508740201635687705 3777677631555151226765779)
                  ·
                    refine ⟨5666516447332726840148669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777677631555151226765779 5666516447332726840148669)
                    ·
                      refine ⟨2124943667749772565055751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666516447332726840148669 2124943667749772565055751)
                      ·
                        rfl

theorem cell23_4138313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_4138313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138313 prefixEnd_4138313 := by exact prefixLift 4138313
  have htrace : WordTrace (prefixWord ++ tailWord_4138313) baseStart_4138313 baseEnd_4138313 := by
    simpa [prefixWord, tailWord_4138313, baseEnd_4138313] using wordTrace_append hprefix tailTrace_4138313
  have hstable : (prefixWord ++ tailWord_4138313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138313).length < 2 ^ (prefixWord ++ tailWord_4138313).sum := by decide
  have hdescent : baseEnd_4138313 < baseStart_4138313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138329 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_4138329 : Nat := 118140960795 + 4138329 * 2 ^ 59
def prefixEnd_4138329 : Nat := 4983230072969 + 3 ^ 40 * 4138329 * 2
def baseEnd_4138329 : Nat := 708317294480081500818559

theorem tailTrace_4138329 : CollatzResearch.WordTrace tailWord_4138329 prefixEnd_4138329 708317294480081500818559 := by
  unfold tailWord_4138329
  simp only [CollatzResearch.WordTrace]
  refine ⟨150937258624548278169450041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100624839083032185446300027 150937258624548278169450041)
  ·
    refine ⟨113202943968411208627087531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150937258624548278169450041 113202943968411208627087531)
    ·
      refine ⟨169804415952616812940631297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113202943968411208627087531 169804415952616812940631297)
      ·
        refine ⟨127353311964462609705473473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169804415952616812940631297 127353311964462609705473473)
        ·
          refine ⟨95514983973346957279105105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127353311964462609705473473 95514983973346957279105105)
          ·
            refine ⟨71636237980010217959328829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95514983973346957279105105 71636237980010217959328829)
            ·
              refine ⟨26863589242503831734748311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71636237980010217959328829 26863589242503831734748311)
              ·
                refine ⟨40295383863755747602122467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26863589242503831734748311 40295383863755747602122467)
                ·
                  refine ⟨60443075795633621403183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40295383863755747602122467 60443075795633621403183701)
                  ·
                    refine ⟨708317294480081500818559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60443075795633621403183701 708317294480081500818559)
                    ·
                      rfl

theorem cell23_4138329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_4138329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138329 prefixEnd_4138329 := by exact prefixLift 4138329
  have htrace : WordTrace (prefixWord ++ tailWord_4138329) baseStart_4138329 baseEnd_4138329 := by
    simpa [prefixWord, tailWord_4138329, baseEnd_4138329] using wordTrace_append hprefix tailTrace_4138329
  have hstable : (prefixWord ++ tailWord_4138329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138329).length < 2 ^ (prefixWord ++ tailWord_4138329).sum := by decide
  have hdescent : baseEnd_4138329 < baseStart_4138329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138353 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_4138353 : Nat := 118140960795 + 4138353 * 2 ^ 59
def prefixEnd_4138353 : Nat := 4983230072969 + 3 ^ 40 * 4138353 * 2
def baseEnd_4138353 : Nat := 2124964206975952408555567

theorem tailTrace_4138353 : CollatzResearch.WordTrace tailWord_4138353 prefixEnd_4138353 2124964206975952408555567 := by
  unfold tailWord_4138353
  simp only [CollatzResearch.WordTrace]
  refine ⟨150938133976461330268323713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100625422650974220178882475 150938133976461330268323713)
  ·
    refine ⟨113203600482345997701242785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150938133976461330268323713 113203600482345997701242785)
    ·
      refine ⟨84902700361759498275932089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113203600482345997701242785 84902700361759498275932089)
      ·
        refine ⟨63677025271319623706949067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84902700361759498275932089 63677025271319623706949067)
        ·
          refine ⟨95515537906979435560423601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63677025271319623706949067 95515537906979435560423601)
          ·
            refine ⟨71636653430234576670317701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95515537906979435560423601 71636653430234576670317701)
            ·
              refine ⟨13431872518168983125684569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71636653430234576670317701 13431872518168983125684569)
              ·
                refine ⟨10073904388626737344263427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13431872518168983125684569 10073904388626737344263427)
                ·
                  refine ⟨15110856582940106016395141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073904388626737344263427 15110856582940106016395141)
                  ·
                    refine ⟨2833285609301269878074089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15110856582940106016395141 2833285609301269878074089)
                    ·
                      refine ⟨2124964206975952408555567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833285609301269878074089 2124964206975952408555567)
                      ·
                        rfl

theorem cell23_4138353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_4138353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138353 prefixEnd_4138353 := by exact prefixLift 4138353
  have htrace : WordTrace (prefixWord ++ tailWord_4138353) baseStart_4138353 baseEnd_4138353 := by
    simpa [prefixWord, tailWord_4138353, baseEnd_4138353] using wordTrace_append hprefix tailTrace_4138353
  have hstable : (prefixWord ++ tailWord_4138353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138353).length < 2 ^ (prefixWord ++ tailWord_4138353).sum := by decide
  have hdescent : baseEnd_4138353 < baseStart_4138353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138357 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4138357 : Nat := 118140960795 + 4138357 * 2 ^ 59
def prefixEnd_4138357 : Nat := 4983230072969 + 3 ^ 40 * 4138357 * 2
def baseEnd_4138357 : Nat := 2124966260898570392905549

theorem tailTrace_4138357 : CollatzResearch.WordTrace tailWord_4138357 prefixEnd_4138357 2124966260898570392905549 := by
  unfold tailWord_4138357
  simp only [CollatzResearch.WordTrace]
  refine ⟨150938279868446838951469325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100625519912297892634312883 150938279868446838951469325)
  ·
    refine ⟨56601854950667564606800997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150938279868446838951469325 56601854950667564606800997)
    ·
      refine ⟨10612847803250168363775187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56601854950667564606800997 10612847803250168363775187)
      ·
        refine ⟨15919271704875252545662781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612847803250168363775187 15919271704875252545662781)
        ·
          refine ⟨5969726889328219704623543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15919271704875252545662781 5969726889328219704623543)
          ·
            refine ⟨8954590333992329556935315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969726889328219704623543 8954590333992329556935315)
            ·
              refine ⟨13431885500988494335402973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954590333992329556935315 13431885500988494335402973)
              ·
                refine ⟨5036957062870685375776115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13431885500988494335402973 5036957062870685375776115)
                ·
                  refine ⟨7555435594306028063664173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036957062870685375776115 7555435594306028063664173)
                  ·
                    refine ⟨2833288347864760523874065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7555435594306028063664173 2833288347864760523874065)
                    ·
                      refine ⟨2124966260898570392905549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833288347864760523874065 2124966260898570392905549)
                      ·
                        rfl

theorem cell23_4138357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4138357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138357 prefixEnd_4138357 := by exact prefixLift 4138357
  have htrace : WordTrace (prefixWord ++ tailWord_4138357) baseStart_4138357 baseEnd_4138357 := by
    simpa [prefixWord, tailWord_4138357, baseEnd_4138357] using wordTrace_append hprefix tailTrace_4138357
  have hstable : (prefixWord ++ tailWord_4138357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138357).length < 2 ^ (prefixWord ++ tailWord_4138357).sum := by decide
  have hdescent : baseEnd_4138357 < baseStart_4138357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138359 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 9]
def baseStart_4138359 : Nat := 118140960795 + 4138359 * 2 ^ 59
def prefixEnd_4138359 : Nat := 4983230072969 + 3 ^ 40 * 4138359 * 2
def baseEnd_4138359 : Nat := 236107476428875487231171

theorem tailTrace_4138359 : CollatzResearch.WordTrace tailWord_4138359 prefixEnd_4138359 236107476428875487231171 := by
  unfold tailWord_4138359
  simp only [CollatzResearch.WordTrace]
  refine ⟨150938352814439593293042131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100625568542959728862028087 150938352814439593293042131)
  ·
    refine ⟨226407529221659389939563197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150938352814439593293042131 226407529221659389939563197)
    ·
      refine ⟨84902823458122271227336199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226407529221659389939563197 84902823458122271227336199)
      ·
        refine ⟨127354235187183406841004299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84902823458122271227336199 127354235187183406841004299)
        ·
          refine ⟨191031352780775110261506449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127354235187183406841004299 191031352780775110261506449)
          ·
            refine ⟨143273514585581332696129837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191031352780775110261506449 143273514585581332696129837)
            ·
              refine ⟨53727567969592999761048689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143273514585581332696129837 53727567969592999761048689)
              ·
                refine ⟨40295675977194749820786517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53727567969592999761048689 40295675977194749820786517)
                ·
                  refine ⟨236107476428875487231171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40295675977194749820786517 236107476428875487231171)
                  ·
                    rfl

theorem cell23_4138359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 9].length) (baseStart_4138359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138359 prefixEnd_4138359 := by exact prefixLift 4138359
  have htrace : WordTrace (prefixWord ++ tailWord_4138359) baseStart_4138359 baseEnd_4138359 := by
    simpa [prefixWord, tailWord_4138359, baseEnd_4138359] using wordTrace_append hprefix tailTrace_4138359
  have hstable : (prefixWord ++ tailWord_4138359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138359).length < 2 ^ (prefixWord ++ tailWord_4138359).sum := by decide
  have hdescent : baseEnd_4138359 < baseStart_4138359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138376 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 7]
def baseStart_4138376 : Nat := 118140960795 + 4138376 * 2 ^ 59
def prefixEnd_4138376 : Nat := 4983230072969 + 3 ^ 40 * 4138376 * 2
def baseEnd_4138376 : Nat := 236108446336778424285329

theorem tailTrace_4138376 : CollatzResearch.WordTrace tailWord_4138376 prefixEnd_4138376 236108446336778424285329 := by
  unfold tailWord_4138376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75469486427689002598205491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100625981903585336797607321 75469486427689002598205491)
  ·
    refine ⟨113204229641533503897308237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75469486427689002598205491 113204229641533503897308237)
    ·
      refine ⟨42451586115575063961490589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113204229641533503897308237 42451586115575063961490589)
      ·
        refine ⟨15919344793340648985558971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42451586115575063961490589 15919344793340648985558971)
        ·
          refine ⟨23879017190010973478338457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919344793340648985558971 23879017190010973478338457)
          ·
            refine ⟨17909262892508230108753843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23879017190010973478338457 17909262892508230108753843)
            ·
              refine ⟨26863894338762345163130765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17909262892508230108753843 26863894338762345163130765)
              ·
                refine ⟨10073960377035879436174037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26863894338762345163130765 10073960377035879436174037)
                ·
                  refine ⟨236108446336778424285329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10073960377035879436174037 236108446336778424285329)
                  ·
                    rfl

theorem cell23_4138376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_4138376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138376 prefixEnd_4138376 := by exact prefixLift 4138376
  have htrace : WordTrace (prefixWord ++ tailWord_4138376) baseStart_4138376 baseEnd_4138376 := by
    simpa [prefixWord, tailWord_4138376, baseEnd_4138376] using wordTrace_append hprefix tailTrace_4138376
  have hstable : (prefixWord ++ tailWord_4138376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138376).length < 2 ^ (prefixWord ++ tailWord_4138376).sum := by decide
  have hdescent : baseEnd_4138376 < baseStart_4138376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138443 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 2, 4, 2]
def baseStart_4138443 : Nat := 118140960795 + 4138443 * 2 ^ 59
def prefixEnd_4138443 : Nat := 4983230072969 + 3 ^ 40 * 4138443 * 2
def baseEnd_4138443 : Nat := 2125010420234857056430153

theorem tailTrace_4138443 : CollatzResearch.WordTrace tailWord_4138443 prefixEnd_4138443 2125010420234857056430153 := by
  unfold tailWord_4138443
  simp only [CollatzResearch.WordTrace]
  refine ⟨150941416546135275639099983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100627611030756850426066655 150941416546135275639099983)
  ·
    refine ⟨226412124819202913458649975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150941416546135275639099983 226412124819202913458649975)
    ·
      refine ⟨339618187228804370187974963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226412124819202913458649975 339618187228804370187974963)
      ·
        refine ⟨509427280843206555281962445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339618187228804370187974963 509427280843206555281962445)
        ·
          refine ⟨191035230316202458230735917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509427280843206555281962445 191035230316202458230735917)
          ·
            refine ⟨71638211368575921836525969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191035230316202458230735917 71638211368575921836525969)
            ·
              refine ⟨53728658526431941377394477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71638211368575921836525969 53728658526431941377394477)
              ·
                refine ⟨20148246947411978016522929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53728658526431941377394477 20148246947411978016522929)
                ·
                  refine ⟨15111185210558983512392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20148246947411978016522929 15111185210558983512392197)
                  ·
                    refine ⟨2833347226979809408573537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15111185210558983512392197 2833347226979809408573537)
                    ·
                      refine ⟨2125010420234857056430153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833347226979809408573537 2125010420234857056430153)
                      ·
                        rfl

theorem cell23_4138443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4, 2].length) (baseStart_4138443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138443 prefixEnd_4138443 := by exact prefixLift 4138443
  have htrace : WordTrace (prefixWord ++ tailWord_4138443) baseStart_4138443 baseEnd_4138443 := by
    simpa [prefixWord, tailWord_4138443, baseEnd_4138443] using wordTrace_append hprefix tailTrace_4138443
  have hstable : (prefixWord ++ tailWord_4138443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138443).length < 2 ^ (prefixWord ++ tailWord_4138443).sum := by decide
  have hdescent : baseEnd_4138443 < baseStart_4138443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138453 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_4138453 : Nat := 118140960795 + 4138453 * 2 ^ 59
def prefixEnd_4138453 : Nat := 4983230072969 + 3 ^ 40 * 4138453 * 2
def baseEnd_4138453 : Nat := 708338518347134005768369

theorem tailTrace_4138453 : CollatzResearch.WordTrace tailWord_4138453 prefixEnd_4138453 708338518347134005768369 := by
  unfold tailWord_4138453
  simp only [CollatzResearch.WordTrace]
  refine ⟨150941781276099047346964013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100627854184066031564642675 150941781276099047346964013)
  ·
    refine ⟨56603167978537142755111505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150941781276099047346964013 56603167978537142755111505)
    ·
      refine ⟨42452375983902857066333629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56603167978537142755111505 42452375983902857066333629)
      ·
        refine ⟨15919640993963571399875111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42452375983902857066333629 15919640993963571399875111)
        ·
          refine ⟨23879461490945357099812667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919640993963571399875111 23879461490945357099812667)
          ·
            refine ⟨35819192236418035649719001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23879461490945357099812667 35819192236418035649719001)
            ·
              refine ⟨26864394177313526737289251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35819192236418035649719001 26864394177313526737289251)
              ·
                refine ⟨40296591265970290105933877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26864394177313526737289251 40296591265970290105933877)
                ·
                  refine ⟨3777805431184714697431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40296591265970290105933877 3777805431184714697431301)
                  ·
                    refine ⟨708338518347134005768369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777805431184714697431301 708338518347134005768369)
                    ·
                      rfl

theorem cell23_4138453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_4138453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138453 prefixEnd_4138453 := by exact prefixLift 4138453
  have htrace : WordTrace (prefixWord ++ tailWord_4138453) baseStart_4138453 baseEnd_4138453 := by
    simpa [prefixWord, tailWord_4138453, baseEnd_4138453] using wordTrace_append hprefix tailTrace_4138453
  have hstable : (prefixWord ++ tailWord_4138453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138453).length < 2 ^ (prefixWord ++ tailWord_4138453).sum := by decide
  have hdescent : baseEnd_4138453 < baseStart_4138453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138456 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4138456 : Nat := 118140960795 + 4138456 * 2 ^ 59
def prefixEnd_4138456 : Nat := 4983230072969 + 3 ^ 40 * 4138456 * 2
def baseEnd_4138456 : Nat := 2125017095483365505567593

theorem tailTrace_4138456 : CollatzResearch.WordTrace tailWord_4138456 prefixEnd_4138456 2125017095483365505567593 := by
  unfold tailWord_4138456
  simp only [CollatzResearch.WordTrace]
  refine ⟨75470945347544089429661611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100627927130058785906215481 75470945347544089429661611)
  ·
    refine ⟨113206418021316134144492417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75470945347544089429661611 113206418021316134144492417)
    ·
      refine ⟨84904813515987100608369313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113206418021316134144492417 84904813515987100608369313)
      ·
        refine ⟨63678610136990325456276985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84904813515987100608369313 63678610136990325456276985)
        ·
          refine ⟨47758957602742744092207739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63678610136990325456276985 47758957602742744092207739)
          ·
            refine ⟨71638436404114116138311609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47758957602742744092207739 71638436404114116138311609)
            ·
              refine ⟨53728827303085587103733707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71638436404114116138311609 53728827303085587103733707)
              ·
                refine ⟨80593240954628380655600561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53728827303085587103733707 80593240954628380655600561)
                ·
                  refine ⟨60444930715971285491700421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80593240954628380655600561 60444930715971285491700421)
                  ·
                    refine ⟨11333424509244616029693829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60444930715971285491700421 11333424509244616029693829)
                    ·
                      refine ⟨2125017095483365505567593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11333424509244616029693829 2125017095483365505567593)
                      ·
                        rfl

theorem cell23_4138456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4138456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138456 prefixEnd_4138456 := by exact prefixLift 4138456
  have htrace : WordTrace (prefixWord ++ tailWord_4138456) baseStart_4138456 baseEnd_4138456 := by
    simpa [prefixWord, tailWord_4138456, baseEnd_4138456] using wordTrace_append hprefix tailTrace_4138456
  have hstable : (prefixWord ++ tailWord_4138456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138456).length < 2 ^ (prefixWord ++ tailWord_4138456).sum := by decide
  have hdescent : baseEnd_4138456 < baseStart_4138456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138494 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4138494 : Nat := 118140960795 + 4138494 * 2 ^ 59
def prefixEnd_4138494 : Nat := 4983230072969 + 3 ^ 40 * 4138494 * 2
def baseEnd_4138494 : Nat := 2125036607748236356892419

theorem tailTrace_4138494 : CollatzResearch.WordTrace tailWord_4138494 prefixEnd_4138494 2125036607748236356892419 := by
  unfold tailWord_4138494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18867909583618813918650817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100628851112633674232804357 18867909583618813918650817)
  ·
    refine ⟨14150932187714110438988113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18867909583618813918650817 14150932187714110438988113)
    ·
      refine ⟨10613199140785582829241085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14150932187714110438988113 10613199140785582829241085)
      ·
        refine ⟨3979949677794593560965407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10613199140785582829241085 3979949677794593560965407)
        ·
          refine ⟨5969924516691890341448111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979949677794593560965407 5969924516691890341448111)
          ·
            refine ⟨8954886775037835512172167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969924516691890341448111 8954886775037835512172167)
            ·
              refine ⟨13432330162556753268258251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954886775037835512172167 13432330162556753268258251)
              ·
                refine ⟨20148495243835129902387377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13432330162556753268258251 20148495243835129902387377)
                ·
                  refine ⟨15111371432876347426790533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20148495243835129902387377 15111371432876347426790533)
                  ·
                    refine ⟨2833382143664315142523225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15111371432876347426790533 2833382143664315142523225)
                    ·
                      refine ⟨2125036607748236356892419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833382143664315142523225 2125036607748236356892419)
                      ·
                        rfl

theorem cell23_4138494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4138494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138494 prefixEnd_4138494 := by exact prefixLift 4138494
  have htrace : WordTrace (prefixWord ++ tailWord_4138494) baseStart_4138494 baseEnd_4138494 := by
    simpa [prefixWord, tailWord_4138494, baseEnd_4138494] using wordTrace_append hprefix tailTrace_4138494
  have hstable : (prefixWord ++ tailWord_4138494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138494).length < 2 ^ (prefixWord ++ tailWord_4138494).sum := by decide
  have hdescent : baseEnd_4138494 < baseStart_4138494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138513 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_4138513 : Nat := 118140960795 + 4138513 * 2 ^ 59
def prefixEnd_4138513 : Nat := 4983230072969 + 3 ^ 40 * 4138513 * 2
def baseEnd_4138513 : Nat := 708348787960223927518277

theorem tailTrace_4138513 : CollatzResearch.WordTrace tailWord_4138513 prefixEnd_4138513 708348787960223927518277 := by
  unfold tailWord_4138513
  simp only [CollatzResearch.WordTrace]
  refine ⟨150943969655881677594148193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100629313103921118396098795 150943969655881677594148193)
  ·
    refine ⟨113207977241911258195611145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150943969655881677594148193 113207977241911258195611145)
    ·
      refine ⟨84905982931433443646708359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113207977241911258195611145 84905982931433443646708359)
      ·
        refine ⟨127358974397150165470062539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84905982931433443646708359 127358974397150165470062539)
        ·
          refine ⟨191038461595725248205093809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127358974397150165470062539 191038461595725248205093809)
          ·
            refine ⟨143278846196793936153820357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191038461595725248205093809 143278846196793936153820357)
            ·
              refine ⟨26864783661898863028841317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143278846196793936153820357 26864783661898863028841317)
              ·
                refine ⟨5037146936606036817907747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26864783661898863028841317 5037146936606036817907747)
                ·
                  refine ⟨7555720404909055226861621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037146936606036817907747 7555720404909055226861621)
                  ·
                    refine ⟨708348787960223927518277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7555720404909055226861621 708348787960223927518277)
                    ·
                      rfl

theorem cell23_4138513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_4138513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138513 prefixEnd_4138513 := by exact prefixLift 4138513
  have htrace : WordTrace (prefixWord ++ tailWord_4138513) baseStart_4138513 baseEnd_4138513 := by
    simpa [prefixWord, tailWord_4138513, baseEnd_4138513] using wordTrace_append hprefix tailTrace_4138513
  have hstable : (prefixWord ++ tailWord_4138513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138513).length < 2 ^ (prefixWord ++ tailWord_4138513).sum := by decide
  have hdescent : baseEnd_4138513 < baseStart_4138513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138527 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 1, 1, 3]
def baseStart_4138527 : Nat := 118140960795 + 4138527 * 2 ^ 59
def prefixEnd_4138527 : Nat := 4983230072969 + 3 ^ 40 * 4138527 * 2
def baseEnd_4138527 : Nat := 2125053552609834727779767

theorem tailTrace_4138527 : CollatzResearch.WordTrace tailWord_4138527 prefixEnd_4138527 2125053552609834727779767 := by
  unfold tailWord_4138527
  simp only [CollatzResearch.WordTrace]
  refine ⟨150944480277830957985157835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100629653518553971990105223 150944480277830957985157835)
  ·
    refine ⟨226416720416746436977736753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150944480277830957985157835 226416720416746436977736753)
    ·
      refine ⟨169812540312559827733302565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226416720416746436977736753 169812540312559827733302565)
      ·
        refine ⟨31839851308604967699994231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169812540312559827733302565 31839851308604967699994231)
        ·
          refine ⟨47759776962907451549991347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31839851308604967699994231 47759776962907451549991347)
          ·
            refine ⟨71639665444361177324987021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47759776962907451549991347 71639665444361177324987021)
            ·
              refine ⟨26864874541635441496870133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71639665444361177324987021 26864874541635441496870133)
              ·
                refine ⟨2518581988278322640331575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26864874541635441496870133 2518581988278322640331575)
                ·
                  refine ⟨3777872982417483960497363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518581988278322640331575 3777872982417483960497363)
                  ·
                    refine ⟨5666809473626225940746045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777872982417483960497363 5666809473626225940746045)
                    ·
                      refine ⟨2125053552609834727779767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666809473626225940746045 2125053552609834727779767)
                      ·
                        rfl

theorem cell23_4138527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_4138527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138527 prefixEnd_4138527 := by exact prefixLift 4138527
  have htrace : WordTrace (prefixWord ++ tailWord_4138527) baseStart_4138527 baseEnd_4138527 := by
    simpa [prefixWord, tailWord_4138527, baseEnd_4138527] using wordTrace_append hprefix tailTrace_4138527
  have hstable : (prefixWord ++ tailWord_4138527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138527).length < 2 ^ (prefixWord ++ tailWord_4138527).sum := by decide
  have hdescent : baseEnd_4138527 < baseStart_4138527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138553 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4138553 : Nat := 118140960795 + 4138553 * 2 ^ 59
def prefixEnd_4138553 : Nat := 4983230072969 + 3 ^ 40 * 4138553 * 2
def baseEnd_4138553 : Nat := 2125066903106851626054647

theorem tailTrace_4138553 : CollatzResearch.WordTrace tailWord_4138553 prefixEnd_4138553 2125066903106851626054647 := by
  unfold tailWord_4138553
  simp only [CollatzResearch.WordTrace]
  refine ⟨150945428575736764425604313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100630285717157842950402875 150945428575736764425604313)
  ·
    refine ⟨113209071431802573319203235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150945428575736764425604313 113209071431802573319203235)
    ·
      refine ⟨169813607147703859978804853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113209071431802573319203235 169813607147703859978804853)
      ·
        refine ⟨15920025670097236873012955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169813607147703859978804853 15920025670097236873012955)
        ·
          refine ⟨23880038505145855309519433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15920025670097236873012955 23880038505145855309519433)
          ·
            refine ⟨17910028878859391482139575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23880038505145855309519433 17910028878859391482139575)
            ·
              refine ⟨26865043318289087223209363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17910028878859391482139575 26865043318289087223209363)
              ·
                refine ⟨40297564977433630834814045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26865043318289087223209363 40297564977433630834814045)
                ·
                  refine ⟨15111586866537611563055267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40297564977433630834814045 15111586866537611563055267)
                  ·
                    refine ⟨22667380299806417344582901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15111586866537611563055267 22667380299806417344582901)
                    ·
                      refine ⟨2125066903106851626054647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22667380299806417344582901 2125066903106851626054647)
                      ·
                        rfl

theorem cell23_4138553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4138553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138553 prefixEnd_4138553 := by exact prefixLift 4138553
  have htrace : WordTrace (prefixWord ++ tailWord_4138553) baseStart_4138553 baseEnd_4138553 := by
    simpa [prefixWord, tailWord_4138553, baseEnd_4138553] using wordTrace_append hprefix tailTrace_4138553
  have hstable : (prefixWord ++ tailWord_4138553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138553).length < 2 ^ (prefixWord ++ tailWord_4138553).sum := by decide
  have hdescent : baseEnd_4138553 < baseStart_4138553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138567 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_4138567 : Nat := 118140960795 + 4138567 * 2 ^ 59
def prefixEnd_4138567 : Nat := 4983230072969 + 3 ^ 40 * 4138567 * 2
def baseEnd_4138567 : Nat := 2125074091836014571279583

theorem tailTrace_4138567 : CollatzResearch.WordTrace tailWord_4138567 prefixEnd_4138567 2125074091836014571279583 := by
  unfold tailWord_4138567
  simp only [CollatzResearch.WordTrace]
  refine ⟨150945939197686044816613955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100630626131790696544409303 150945939197686044816613955)
  ·
    refine ⟨226418908796529067224920933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150945939197686044816613955 226418908796529067224920933)
    ·
      refine ⟨42453545399349200104672675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226418908796529067224920933 42453545399349200104672675)
      ·
        refine ⟨63680318099023800157009013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42453545399349200104672675 63680318099023800157009013)
        ·
          refine ⟨5970029821783481264719595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63680318099023800157009013 5970029821783481264719595)
          ·
            refine ⟨8955044732675221897079393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970029821783481264719595 8955044732675221897079393)
            ·
              refine ⟨6716283549506416422809545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955044732675221897079393 6716283549506416422809545)
              ·
                refine ⟨5037212662129812317107159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716283549506416422809545 5037212662129812317107159)
                ·
                  refine ⟨7555818993194718475660739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037212662129812317107159 7555818993194718475660739)
                  ·
                    refine ⟨11333728489792077713491109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7555818993194718475660739 11333728489792077713491109)
                    ·
                      refine ⟨2125074091836014571279583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11333728489792077713491109 2125074091836014571279583)
                      ·
                        rfl

theorem cell23_4138567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_4138567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138567 prefixEnd_4138567 := by exact prefixLift 4138567
  have htrace : WordTrace (prefixWord ++ tailWord_4138567) baseStart_4138567 baseEnd_4138567 := by
    simpa [prefixWord, tailWord_4138567, baseEnd_4138567] using wordTrace_append hprefix tailTrace_4138567
  have hstable : (prefixWord ++ tailWord_4138567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138567).length < 2 ^ (prefixWord ++ tailWord_4138567).sum := by decide
  have hdescent : baseEnd_4138567 < baseStart_4138567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138617 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 3]
def baseStart_4138617 : Nat := 118140960795 + 4138617 * 2 ^ 59
def prefixEnd_4138617 : Nat := 4983230072969 + 3 ^ 40 * 4138617 * 2
def baseEnd_4138617 : Nat := 2125099765868739375654353

theorem tailTrace_4138617 : CollatzResearch.WordTrace tailWord_4138617 prefixEnd_4138617 2125099765868739375654353 := by
  unfold tailWord_4138617
  simp only [CollatzResearch.WordTrace]
  refine ⟨150947762847504903355934105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100631841898336602237289403 150947762847504903355934105)
  ·
    refine ⟨113210822135628677516950579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150947762847504903355934105 113210822135628677516950579)
    ·
      refine ⟨169816233203443016275425869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113210822135628677516950579 169816233203443016275425869)
      ·
        refine ⟨63681087451291131103284701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169816233203443016275425869 63681087451291131103284701)
        ·
          refine ⟨23880407794234174163731763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63681087451291131103284701 23880407794234174163731763)
          ·
            refine ⟨35820611691351261245597645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23880407794234174163731763 35820611691351261245597645)
            ·
              refine ⟨13432729384256722967099117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35820611691351261245597645 13432729384256722967099117)
              ·
                refine ⟨5037273519096271112662169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13432729384256722967099117 5037273519096271112662169)
                ·
                  refine ⟨3777955139322203334496627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037273519096271112662169 3777955139322203334496627)
                  ·
                    refine ⟨5666932708983305001744941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777955139322203334496627 5666932708983305001744941)
                    ·
                      refine ⟨2125099765868739375654353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666932708983305001744941 2125099765868739375654353)
                      ·
                        rfl

theorem cell23_4138617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_4138617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138617 prefixEnd_4138617 := by exact prefixLift 4138617
  have htrace : WordTrace (prefixWord ++ tailWord_4138617) baseStart_4138617 baseEnd_4138617 := by
    simpa [prefixWord, tailWord_4138617, baseEnd_4138617] using wordTrace_append hprefix tailTrace_4138617
  have hstable : (prefixWord ++ tailWord_4138617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138617).length < 2 ^ (prefixWord ++ tailWord_4138617).sum := by decide
  have hdescent : baseEnd_4138617 < baseStart_4138617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138643 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3]
def baseStart_4138643 : Nat := 118140960795 + 4138643 * 2 ^ 59
def prefixEnd_4138643 : Nat := 4983230072969 + 3 ^ 40 * 4138643 * 2
def baseEnd_4138643 : Nat := 2125113116365756273929233

theorem tailTrace_4138643 : CollatzResearch.WordTrace tailWord_4138643 prefixEnd_4138643 2125113116365756273929233 := by
  unfold tailWord_4138643
  simp only [CollatzResearch.WordTrace]
  refine ⟨150948711145410709796380583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100632474096940473197587055 150948711145410709796380583)
  ·
    refine ⟨226423066718116064694570875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150948711145410709796380583 226423066718116064694570875)
    ·
      refine ⟨339634600077174097041856313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226423066718116064694570875 339634600077174097041856313)
      ·
        refine ⟨254725950057880572781392235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339634600077174097041856313 254725950057880572781392235)
        ·
          refine ⟨382088925086820859172088353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254725950057880572781392235 382088925086820859172088353)
          ·
            refine ⟨286566693815115644379066265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382088925086820859172088353 286566693815115644379066265)
            ·
              refine ⟨214925020361336733284299699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286566693815115644379066265 214925020361336733284299699)
              ·
                refine ⟨322387530542005099926449549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214925020361336733284299699 322387530542005099926449549)
                ·
                  refine ⟨120895323953251912472418581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322387530542005099926449549 120895323953251912472418581)
                  ·
                    refine ⟨5666968310308683397144621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120895323953251912472418581 5666968310308683397144621)
                    ·
                      refine ⟨2125113116365756273929233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666968310308683397144621 2125113116365756273929233)
                      ·
                        rfl

theorem cell23_4138643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_4138643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138643 prefixEnd_4138643 := by exact prefixLift 4138643
  have htrace : WordTrace (prefixWord ++ tailWord_4138643) baseStart_4138643 baseEnd_4138643 := by
    simpa [prefixWord, tailWord_4138643, baseEnd_4138643] using wordTrace_append hprefix tailTrace_4138643
  have hstable : (prefixWord ++ tailWord_4138643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138643).length < 2 ^ (prefixWord ++ tailWord_4138643).sum := by decide
  have hdescent : baseEnd_4138643 < baseStart_4138643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138653 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4138653 : Nat := 118140960795 + 4138653 * 2 ^ 59
def prefixEnd_4138653 : Nat := 4983230072969 + 3 ^ 40 * 4138653 * 2
def baseEnd_4138653 : Nat := 2125118251172301234804187

theorem tailTrace_4138653 : CollatzResearch.WordTrace tailWord_4138653 prefixEnd_4138653 2125118251172301234804187 := by
  unfold tailWord_4138653
  simp only [CollatzResearch.WordTrace]
  refine ⟨150949075875374481504244613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100632717250249654336163075 150949075875374481504244613)
  ·
    refine ⟨28302951726632715282045865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150949075875374481504244613 28302951726632715282045865)
    ·
      refine ⟨21227213794974536461534399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28302951726632715282045865 21227213794974536461534399)
      ·
        refine ⟨31840820692461804692301599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227213794974536461534399 31840820692461804692301599)
        ·
          refine ⟨47761231038692707038452399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31840820692461804692301599 47761231038692707038452399)
          ·
            refine ⟨71641846558039060557678599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47761231038692707038452399 71641846558039060557678599)
            ·
              refine ⟨107462769837058590836517899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71641846558039060557678599 107462769837058590836517899)
              ·
                refine ⟨161194154755587886254776849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107462769837058590836517899 161194154755587886254776849)
                ·
                  refine ⟨120895616066690914691082637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161194154755587886254776849 120895616066690914691082637)
                  ·
                    refine ⟨45335856025009093009155989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120895616066690914691082637 45335856025009093009155989)
                    ·
                      refine ⟨2125118251172301234804187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45335856025009093009155989 2125118251172301234804187)
                      ·
                        rfl

theorem cell23_4138653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4138653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138653 prefixEnd_4138653 := by exact prefixLift 4138653
  have htrace : WordTrace (prefixWord ++ tailWord_4138653) baseStart_4138653 baseEnd_4138653 := by
    simpa [prefixWord, tailWord_4138653, baseEnd_4138653] using wordTrace_append hprefix tailTrace_4138653
  have hstable : (prefixWord ++ tailWord_4138653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138653).length < 2 ^ (prefixWord ++ tailWord_4138653).sum := by decide
  have hdescent : baseEnd_4138653 < baseStart_4138653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138660 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_4138660 : Nat := 118140960795 + 4138660 * 2 ^ 59
def prefixEnd_4138660 : Nat := 4983230072969 + 3 ^ 40 * 4138660 * 2
def baseEnd_4138660 : Nat := 2125121845536882707416655

theorem tailTrace_4138660 : CollatzResearch.WordTrace tailWord_4138660 prefixEnd_4138660 2125121845536882707416655 := by
  unfold tailWord_4138660
  simp only [CollatzResearch.WordTrace]
  refine ⟨75474665593174560849874717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100632887457566081133166289 75474665593174560849874717)
  ·
    refine ⟨28302999597440460318703019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75474665593174560849874717 28302999597440460318703019)
    ·
      refine ⟨42454499396160690478054529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28302999597440460318703019 42454499396160690478054529)
      ·
        refine ⟨31840874547120517858540897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42454499396160690478054529 31840874547120517858540897)
        ·
          refine ⟨23880655910340388393905673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31840874547120517858540897 23880655910340388393905673)
          ·
            refine ⟨17910491932755291295429255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23880655910340388393905673 17910491932755291295429255)
            ·
              refine ⟨26865737899132936943143883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17910491932755291295429255 26865737899132936943143883)
              ·
                refine ⟨40298606848699405414715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26865737899132936943143883 40298606848699405414715825)
                ·
                  refine ⟨30223955136524554061036869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40298606848699405414715825 30223955136524554061036869)
                  ·
                    refine ⟨5666991588098353886444413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30223955136524554061036869 5666991588098353886444413)
                    ·
                      refine ⟨2125121845536882707416655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5666991588098353886444413 2125121845536882707416655)
                      ·
                        rfl

theorem cell23_4138660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_4138660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138660 prefixEnd_4138660 := by exact prefixLift 4138660
  have htrace : WordTrace (prefixWord ++ tailWord_4138660) baseStart_4138660 baseEnd_4138660 := by
    simpa [prefixWord, tailWord_4138660, baseEnd_4138660] using wordTrace_append hprefix tailTrace_4138660
  have hstable : (prefixWord ++ tailWord_4138660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138660).length < 2 ^ (prefixWord ++ tailWord_4138660).sum := by decide
  have hdescent : baseEnd_4138660 < baseStart_4138660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138674 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_4138674 : Nat := 118140960795 + 4138674 * 2 ^ 59
def prefixEnd_4138674 : Nat := 4983230072969 + 3 ^ 40 * 4138674 * 2
def baseEnd_4138674 : Nat := 2125129034266045652641591

theorem tailTrace_4138674 : CollatzResearch.WordTrace tailWord_4138674 prefixEnd_4138674 2125129034266045652641591 := by
  unfold tailWord_4138674
  simp only [CollatzResearch.WordTrace]
  refine ⟨37737460452074600522689769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100633227872198934727172717 37737460452074600522689769)
  ·
    refine ⟨28303095339055950392017327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37737460452074600522689769 28303095339055950392017327)
    ·
      refine ⟨42454643008583925588025991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28303095339055950392017327 42454643008583925588025991)
      ·
        refine ⟨63681964512875888382038987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42454643008583925588025991 63681964512875888382038987)
        ·
          refine ⟨95522946769313832573058481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63681964512875888382038987 95522946769313832573058481)
          ·
            refine ⟨71642210076985374429793861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95522946769313832573058481 71642210076985374429793861)
            ·
              refine ⟨13432914389434757705586349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71642210076985374429793861 13432914389434757705586349)
              ·
                refine ⟨5037342896038034139594881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13432914389434757705586349 5037342896038034139594881)
                ·
                  refine ⟨3778007172028525604696161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037342896038034139594881 3778007172028525604696161)
                  ·
                    refine ⟨2833505379021394203522121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3778007172028525604696161 2833505379021394203522121)
                    ·
                      refine ⟨2125129034266045652641591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833505379021394203522121 2125129034266045652641591)
                      ·
                        rfl

theorem cell23_4138674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_4138674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138674 prefixEnd_4138674 := by exact prefixLift 4138674
  have htrace : WordTrace (prefixWord ++ tailWord_4138674) baseStart_4138674 baseEnd_4138674 := by
    simpa [prefixWord, tailWord_4138674, baseEnd_4138674] using wordTrace_append hprefix tailTrace_4138674
  have hstable : (prefixWord ++ tailWord_4138674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138674).length < 2 ^ (prefixWord ++ tailWord_4138674).sum := by decide
  have hdescent : baseEnd_4138674 < baseStart_4138674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138693 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_4138693 : Nat := 118140960795 + 4138693 * 2 ^ 59
def prefixEnd_4138693 : Nat := 4983230072969 + 3 ^ 40 * 4138693 * 2
def baseEnd_4138693 : Nat := 708379596799493692768001

theorem tailTrace_4138693 : CollatzResearch.WordTrace tailWord_4138693 prefixEnd_4138693 708379596799493692768001 := by
  unfold tailWord_4138693
  simp only [CollatzResearch.WordTrace]
  refine ⟨150950534795229568335700733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100633689863486378890467155 150950534795229568335700733)
  ·
    refine ⟨56606450548211088125887775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150950534795229568335700733 56606450548211088125887775)
    ·
      refine ⟨84909675822316632188831663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56606450548211088125887775 84909675822316632188831663)
      ·
        refine ⟨127364513733474948283247495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84909675822316632188831663 127364513733474948283247495)
        ·
          refine ⟨191046770600212422424871243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127364513733474948283247495 191046770600212422424871243)
          ·
            refine ⟨286570155900318633637306865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191046770600212422424871243 286570155900318633637306865)
            ·
              refine ⟨214927616925238975227980149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286570155900318633637306865 214927616925238975227980149)
              ·
                refine ⟨20149464086741153927623139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214927616925238975227980149 20149464086741153927623139)
                ·
                  refine ⟨30224196130111730891434709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20149464086741153927623139 30224196130111730891434709)
                  ·
                    refine ⟨708379596799493692768001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30224196130111730891434709 708379596799493692768001)
                    ·
                      rfl

theorem cell23_4138693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_4138693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138693 prefixEnd_4138693 := by exact prefixLift 4138693
  have htrace : WordTrace (prefixWord ++ tailWord_4138693) baseStart_4138693 baseEnd_4138693 := by
    simpa [prefixWord, tailWord_4138693, baseEnd_4138693] using wordTrace_append hprefix tailTrace_4138693
  have hstable : (prefixWord ++ tailWord_4138693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138693).length < 2 ^ (prefixWord ++ tailWord_4138693).sum := by decide
  have hdescent : baseEnd_4138693 < baseStart_4138693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138703 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_4138703 : Nat := 118140960795 + 4138703 * 2 ^ 59
def prefixEnd_4138703 : Nat := 4983230072969 + 3 ^ 40 * 4138703 * 2
def baseEnd_4138703 : Nat := 2125143925205026039178957

theorem tailTrace_4138703 : CollatzResearch.WordTrace tailWord_4138703 prefixEnd_4138703 2125143925205026039178957 := by
  unfold tailWord_4138703
  simp only [CollatzResearch.WordTrace]
  refine ⟨150950899525193340043564763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100633933016795560029043175 150950899525193340043564763)
  ·
    refine ⟨226426349287790010065347145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150950899525193340043564763 226426349287790010065347145)
    ·
      refine ⟨169819761965842507549010359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226426349287790010065347145 169819761965842507549010359)
      ·
        refine ⟨254729642948763761323515539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169819761965842507549010359 254729642948763761323515539)
        ·
          refine ⟨382094464423145641985273309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254729642948763761323515539 382094464423145641985273309)
          ·
            refine ⟨143285424158679615744477491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382094464423145641985273309 143285424158679615744477491)
            ·
              refine ⟨214928136238019423616716237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143285424158679615744477491 214928136238019423616716237)
              ·
                refine ⟨80598051089257283856268589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214928136238019423616716237 80598051089257283856268589)
                ·
                  refine ⟨30224269158471481446100721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80598051089257283856268589 30224269158471481446100721)
                  ·
                    refine ⟨22668201868853611084575541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30224269158471481446100721 22668201868853611084575541)
                    ·
                      refine ⟨2125143925205026039178957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22668201868853611084575541 2125143925205026039178957)
                      ·
                        rfl

theorem cell23_4138703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_4138703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138703 prefixEnd_4138703 := by exact prefixLift 4138703
  have htrace : WordTrace (prefixWord ++ tailWord_4138703) baseStart_4138703 baseEnd_4138703 := by
    simpa [prefixWord, tailWord_4138703, baseEnd_4138703] using wordTrace_append hprefix tailTrace_4138703
  have hstable : (prefixWord ++ tailWord_4138703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138703).length < 2 ^ (prefixWord ++ tailWord_4138703).sum := by decide
  have hdescent : baseEnd_4138703 < baseStart_4138703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138708 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4138708 : Nat := 118140960795 + 4138708 * 2 ^ 59
def prefixEnd_4138708 : Nat := 4983230072969 + 3 ^ 40 * 4138708 * 2
def baseEnd_4138708 : Nat := 2125146492608298519616435

theorem tailTrace_4138708 : CollatzResearch.WordTrace tailWord_4138708 prefixEnd_4138708 2125146492608298519616435 := by
  unfold tailWord_4138708
  simp only [CollatzResearch.WordTrace]
  refine ⟨75475540945087612948748389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100634054593450150598331185 75475540945087612948748389)
  ·
    refine ⟨14151663927203927427890323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75475540945087612948748389 14151663927203927427890323)
    ·
      refine ⟨21227495890805891141835485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14151663927203927427890323 21227495890805891141835485)
      ·
        refine ⟨7960310959052209178188307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21227495890805891141835485 7960310959052209178188307)
        ·
          refine ⟨11940466438578313767282461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960310959052209178188307 11940466438578313767282461)
          ·
            refine ⟨4477674914466867662730923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11940466438578313767282461 4477674914466867662730923)
            ·
              refine ⟨6716512371700301494096385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477674914466867662730923 6716512371700301494096385)
              ·
                refine ⟨5037384278775226120572289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716512371700301494096385 5037384278775226120572289)
                ·
                  refine ⟨3778038209081419590429217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037384278775226120572289 3778038209081419590429217)
                  ·
                    refine ⟨2833528656811064692821913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3778038209081419590429217 2833528656811064692821913)
                    ·
                      refine ⟨2125146492608298519616435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833528656811064692821913 2125146492608298519616435)
                      ·
                        rfl

theorem cell23_4138708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4138708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138708 prefixEnd_4138708 := by exact prefixLift 4138708
  have htrace : WordTrace (prefixWord ++ tailWord_4138708) baseStart_4138708 baseEnd_4138708 := by
    simpa [prefixWord, tailWord_4138708, baseEnd_4138708] using wordTrace_append hprefix tailTrace_4138708
  have hstable : (prefixWord ++ tailWord_4138708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138708).length < 2 ^ (prefixWord ++ tailWord_4138708).sum := by decide
  have hdescent : baseEnd_4138708 < baseStart_4138708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138730 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4138730 : Nat := 118140960795 + 4138730 * 2 ^ 59
def prefixEnd_4138730 : Nat := 4983230072969 + 3 ^ 40 * 4138730 * 2
def baseEnd_4138730 : Nat := 2125157789182697433541333

theorem tailTrace_4138730 : CollatzResearch.WordTrace tailWord_4138730 prefixEnd_4138730 2125157789182697433541333 := by
  unfold tailWord_4138730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37737971074023880913699411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100634589530730349103198429 37737971074023880913699411)
  ·
    refine ⟨56606956611035821370549117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37737971074023880913699411 56606956611035821370549117)
    ·
      refine ⟨21227608729138433013955919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56606956611035821370549117 21227608729138433013955919)
      ·
        refine ⟨31841413093707649520933879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227608729138433013955919 31841413093707649520933879)
        ·
          refine ⟨47762119640561474281400819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31841413093707649520933879 47762119640561474281400819)
          ·
            refine ⟨71643179460842211422101229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47762119640561474281400819 71643179460842211422101229)
            ·
              refine ⟨26866192297815829283287961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71643179460842211422101229 26866192297815829283287961)
              ·
                refine ⟨20149644223361871962465971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26866192297815829283287961 20149644223361871962465971)
                ·
                  refine ⟨30224466335042807943698957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20149644223361871962465971 30224466335042807943698957)
                  ·
                    refine ⟨11334174875641052978887109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30224466335042807943698957 11334174875641052978887109)
                    ·
                      refine ⟨2125157789182697433541333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11334174875641052978887109 2125157789182697433541333)
                      ·
                        rfl

theorem cell23_4138730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4138730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138730 prefixEnd_4138730 := by exact prefixLift 4138730
  have htrace : WordTrace (prefixWord ++ tailWord_4138730) baseStart_4138730 baseEnd_4138730 := by
    simpa [prefixWord, tailWord_4138730, baseEnd_4138730] using wordTrace_append hprefix tailTrace_4138730
  have hstable : (prefixWord ++ tailWord_4138730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138730).length < 2 ^ (prefixWord ++ tailWord_4138730).sum := by decide
  have hdescent : baseEnd_4138730 < baseStart_4138730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138765 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 7]
def baseStart_4138765 : Nat := 118140960795 + 4138765 * 2 ^ 59
def prefixEnd_4138765 : Nat := 4983230072969 + 3 ^ 40 * 4138765 * 2
def baseEnd_4138765 : Nat := 236130640111733866289297

theorem tailTrace_4138765 : CollatzResearch.WordTrace tailWord_4138765 prefixEnd_4138765 236130640111733866289297 := by
  unfold tailWord_4138765
  simp only [CollatzResearch.WordTrace]
  refine ⟨150953160850968724632321749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100635440567312483088214499 150953160850968724632321749)
  ·
    refine ⟨3537964707444579483570041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 150953160850968724632321749 3537964707444579483570041)
    ·
      refine ⟨2653473530583434612677531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3537964707444579483570041 2653473530583434612677531)
      ·
        refine ⟨3980210295875151919016297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653473530583434612677531 3980210295875151919016297)
        ·
          refine ⟨2985157721906363939262223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3980210295875151919016297 2985157721906363939262223)
          ·
            refine ⟨4477736582859545908893335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985157721906363939262223 4477736582859545908893335)
            ·
              refine ⟨6716604874289318863340003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477736582859545908893335 6716604874289318863340003)
              ·
                refine ⟨10074907311433978295010005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716604874289318863340003 10074907311433978295010005)
                ·
                  refine ⟨236130640111733866289297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10074907311433978295010005 236130640111733866289297)
                  ·
                    rfl

theorem cell23_4138765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_4138765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138765 prefixEnd_4138765 := by exact prefixLift 4138765
  have htrace : WordTrace (prefixWord ++ tailWord_4138765) baseStart_4138765 baseEnd_4138765 := by
    simpa [prefixWord, tailWord_4138765, baseEnd_4138765] using wordTrace_append hprefix tailTrace_4138765
  have hstable : (prefixWord ++ tailWord_4138765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138765).length < 2 ^ (prefixWord ++ tailWord_4138765).sum := by decide
  have hdescent : baseEnd_4138765 < baseStart_4138765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
