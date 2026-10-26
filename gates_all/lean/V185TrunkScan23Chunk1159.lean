import V185TrunkScan23Chunk1158

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6865990 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_6865990 : Nat := 118140960795 + 6865990 * 2 ^ 59
def prefixEnd_6865990 : Nat := 4983230072969 + 3 ^ 40 * 6865990 * 2
def baseEnd_6865990 : Nat := 1175184346321232338749631

theorem tailTrace_6865990 : CollatzResearch.WordTrace tailWord_6865990 prefixEnd_6865990 1175184346321232338749631 := by
  unfold tailWord_6865990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825725887365572580632607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166948818930465548386828949 7825725887365572580632607)
  ·
    refine ⟨11738588831048358870948911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7825725887365572580632607 11738588831048358870948911)
    ·
      refine ⟨17607883246572538306423367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738588831048358870948911 17607883246572538306423367)
      ·
        refine ⟨26411824869858807459635051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607883246572538306423367 26411824869858807459635051)
        ·
          refine ⟨39617737304788211189452577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26411824869858807459635051 39617737304788211189452577)
          ·
            refine ⟨29713302978591158392089433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39617737304788211189452577 29713302978591158392089433)
            ·
              refine ⟨22284977233943368794067075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29713302978591158392089433 22284977233943368794067075)
              ·
                refine ⟨33427465850915053191100613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22284977233943368794067075 33427465850915053191100613)
                ·
                  refine ⟨6267649847046572473331365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33427465850915053191100613 6267649847046572473331365)
                  ·
                    refine ⟨1175184346321232338749631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267649847046572473331365 1175184346321232338749631)
                    ·
                      rfl

theorem cell23_6865990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_6865990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865990 prefixEnd_6865990 := by exact prefixLift 6865990
  have htrace : WordTrace (prefixWord ++ tailWord_6865990) baseStart_6865990 baseEnd_6865990 := by
    simpa [prefixWord, tailWord_6865990, baseEnd_6865990] using wordTrace_append hprefix tailTrace_6865990
  have hstable : (prefixWord ++ tailWord_6865990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865990).length < 2 ^ (prefixWord ++ tailWord_6865990).sum := by decide
  have hdescent : baseEnd_6865990 < baseStart_6865990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6865997 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_6865997 : Nat := 118140960795 + 6865997 * 2 ^ 59
def prefixEnd_6865997 : Nat := 4983230072969 + 3 ^ 40 * 6865997 * 2
def baseEnd_6865997 : Nat := 3525556633328278488861361

theorem tailTrace_6865997 : CollatzResearch.WordTrace tailWord_6865997 prefixEnd_6865997 3525556633328278488861361 := by
  unfold tailWord_6865997
  simp only [CollatzResearch.WordTrace]
  refine ⟨250423483706672962775748245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166948989137781975183832163 250423483706672962775748245)
  ·
    refine ⟨11738600798750295130113199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250423483706672962775748245 11738600798750295130113199)
    ·
      refine ⟨17607901198125442695169799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738600798750295130113199 17607901198125442695169799)
      ·
        refine ⟨26411851797188164042754699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607901198125442695169799 26411851797188164042754699)
        ·
          refine ⟨39617777695782246064132049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26411851797188164042754699 39617777695782246064132049)
          ·
            refine ⟨29713333271836684548099037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39617777695782246064132049 29713333271836684548099037)
            ·
              refine ⟨11142499976938756705537139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29713333271836684548099037 11142499976938756705537139)
              ·
                refine ⟨16713749965408135058305709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142499976938756705537139 16713749965408135058305709)
                ·
                  refine ⟨6267656237028050646864641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16713749965408135058305709 6267656237028050646864641)
                  ·
                    refine ⟨4700742177771037985148481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267656237028050646864641 4700742177771037985148481)
                    ·
                      refine ⟨3525556633328278488861361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700742177771037985148481 3525556633328278488861361)
                      ·
                        rfl

theorem cell23_6865997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_6865997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6865997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6865997 prefixEnd_6865997 := by exact prefixLift 6865997
  have htrace : WordTrace (prefixWord ++ tailWord_6865997) baseStart_6865997 baseEnd_6865997 := by
    simpa [prefixWord, tailWord_6865997, baseEnd_6865997] using wordTrace_append hprefix tailTrace_6865997
  have hstable : (prefixWord ++ tailWord_6865997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6865997).length < 2 ^ (prefixWord ++ tailWord_6865997).sum := by decide
  have hdescent : baseEnd_6865997 < baseStart_6865997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6865997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866009 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6866009 : Nat := 118140960795 + 6866009 * 2 ^ 59
def prefixEnd_6866009 : Nat := 4983230072969 + 3 ^ 40 * 6866009 * 2
def baseEnd_6866009 : Nat := 3525562795096132441911305

theorem tailTrace_6866009 : CollatzResearch.WordTrace tailWord_6866009 prefixEnd_6866009 3525562795096132441911305 := by
  unfold tailWord_6866009
  simp only [CollatzResearch.WordTrace]
  refine ⟨250423921382629488825185081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166949280921752992550123387 250423921382629488825185081)
  ·
    refine ⟨187817941036972116618888811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250423921382629488825185081 187817941036972116618888811)
    ·
      refine ⟨281726911555458174928333217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187817941036972116618888811 281726911555458174928333217)
      ·
        refine ⟨211295183666593631196249913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281726911555458174928333217 211295183666593631196249913)
        ·
          refine ⟨158471387749945223397187435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211295183666593631196249913 158471387749945223397187435)
          ·
            refine ⟨237707081624917835095781153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158471387749945223397187435 237707081624917835095781153)
            ·
              refine ⟨178280311218688376321835865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237707081624917835095781153 178280311218688376321835865)
              ·
                refine ⟨133710233414016282241376899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178280311218688376321835865 133710233414016282241376899)
                ·
                  refine ⟨200565350121024423362065349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133710233414016282241376899 200565350121024423362065349)
                  ·
                    refine ⟨37606003147692079380387253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200565350121024423362065349 37606003147692079380387253)
                    ·
                      refine ⟨3525562795096132441911305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37606003147692079380387253 3525562795096132441911305)
                      ·
                        rfl

theorem cell23_6866009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6866009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866009 prefixEnd_6866009 := by exact prefixLift 6866009
  have htrace : WordTrace (prefixWord ++ tailWord_6866009) baseStart_6866009 baseEnd_6866009 := by
    simpa [prefixWord, tailWord_6866009, baseEnd_6866009] using wordTrace_append hprefix tailTrace_6866009
  have hstable : (prefixWord ++ tailWord_6866009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866009).length < 2 ^ (prefixWord ++ tailWord_6866009).sum := by decide
  have hdescent : baseEnd_6866009 < baseStart_6866009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866014 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6866014 : Nat := 118140960795 + 6866014 * 2 ^ 59
def prefixEnd_6866014 : Nat := 4983230072969 + 3 ^ 40 * 6866014 * 2
def baseEnd_6866014 : Nat := 3525565362499404922348783

theorem tailTrace_6866014 : CollatzResearch.WordTrace tailWord_6866014 prefixEnd_6866014 3525565362499404922348783 := by
  unfold tailWord_6866014
  simp only [CollatzResearch.WordTrace]
  refine ⟨31303012968451421834889637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166949402498407583119411397 31303012968451421834889637)
  ·
    refine ⟨5869314931584641594041807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31303012968451421834889637 5869314931584641594041807)
    ·
      refine ⟨8803972397376962391062711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869314931584641594041807 8803972397376962391062711)
      ·
        refine ⟨13205958596065443586594067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803972397376962391062711 13205958596065443586594067)
        ·
          refine ⟨19808937894098165379891101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205958596065443586594067 19808937894098165379891101)
          ·
            refine ⟨7428351710286812017459163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19808937894098165379891101 7428351710286812017459163)
            ·
              refine ⟨11142527565430218026188745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428351710286812017459163 11142527565430218026188745)
              ·
                refine ⟨8356895674072663519641559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11142527565430218026188745 8356895674072663519641559)
                ·
                  refine ⟨12535343511108995279462339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8356895674072663519641559 12535343511108995279462339)
                  ·
                    refine ⟨18803015266663492919193509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12535343511108995279462339 18803015266663492919193509)
                    ·
                      refine ⟨3525565362499404922348783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18803015266663492919193509 3525565362499404922348783)
                      ·
                        rfl

theorem cell23_6866014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6866014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866014 prefixEnd_6866014 := by exact prefixLift 6866014
  have htrace : WordTrace (prefixWord ++ tailWord_6866014) baseStart_6866014 baseEnd_6866014 := by
    simpa [prefixWord, tailWord_6866014, baseEnd_6866014] using wordTrace_append hprefix tailTrace_6866014
  have hstable : (prefixWord ++ tailWord_6866014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866014).length < 2 ^ (prefixWord ++ tailWord_6866014).sum := by decide
  have hdescent : baseEnd_6866014 < baseStart_6866014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866019 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6866019 : Nat := 118140960795 + 6866019 * 2 ^ 59
def prefixEnd_6866019 : Nat := 4983230072969 + 3 ^ 40 * 6866019 * 2
def baseEnd_6866019 : Nat := 3525567929902677402786259

theorem tailTrace_6866019 : CollatzResearch.WordTrace tailWord_6866019 prefixEnd_6866019 3525567929902677402786259 := by
  unfold tailWord_6866019
  simp only [CollatzResearch.WordTrace]
  refine ⟨250424286112593260533049111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166949524075062173688699407 250424286112593260533049111)
  ·
    refine ⟨375636429168889890799573667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250424286112593260533049111 375636429168889890799573667)
    ·
      refine ⟨563454643753334836199360501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375636429168889890799573667 563454643753334836199360501)
      ·
        refine ⟨52823872851875140893690047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 563454643753334836199360501 52823872851875140893690047)
        ·
          refine ⟨79235809277812711340535071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52823872851875140893690047 79235809277812711340535071)
          ·
            refine ⟨118853713916719067010802607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79235809277812711340535071 118853713916719067010802607)
            ·
              refine ⟨178280570875078600516203911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118853713916719067010802607 178280570875078600516203911)
              ·
                refine ⟨267420856312617900774305867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178280570875078600516203911 267420856312617900774305867)
                ·
                  refine ⟨401131284468926851161458801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267420856312617900774305867 401131284468926851161458801)
                  ·
                    refine ⟨300848463351695138371094101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 401131284468926851161458801 300848463351695138371094101)
                    ·
                      refine ⟨3525567929902677402786259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 300848463351695138371094101 3525567929902677402786259)
                      ·
                        rfl

theorem cell23_6866019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6866019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866019 prefixEnd_6866019 := by exact prefixLift 6866019
  have htrace : WordTrace (prefixWord ++ tailWord_6866019) baseStart_6866019 baseEnd_6866019 := by
    simpa [prefixWord, tailWord_6866019, baseEnd_6866019] using wordTrace_append hprefix tailTrace_6866019
  have hstable : (prefixWord ++ tailWord_6866019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866019).length < 2 ^ (prefixWord ++ tailWord_6866019).sum := by decide
  have hdescent : baseEnd_6866019 < baseStart_6866019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866059 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 11]
def baseStart_6866059 : Nat := 118140960795 + 6866059 * 2 ^ 59
def prefixEnd_6866059 : Nat := 4983230072969 + 3 ^ 40 * 6866059 * 2
def baseEnd_6866059 : Nat := 391732052125428582920675

theorem tailTrace_6866059 : CollatzResearch.WordTrace tailWord_6866059 prefixEnd_6866059 391732052125428582920675 := by
  unfold tailWord_6866059
  simp only [CollatzResearch.WordTrace]
  refine ⟨250425745032448347364505231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166950496688298898243003487 250425745032448347364505231)
  ·
    refine ⟨375638617548672521046757847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250425745032448347364505231 375638617548672521046757847)
    ·
      refine ⟨563457926323008781570136771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375638617548672521046757847 563457926323008781570136771)
      ·
        refine ⟨845186889484513172355205157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563457926323008781570136771 845186889484513172355205157)
        ·
          refine ⟨158472541778346219816600967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 845186889484513172355205157 158472541778346219816600967)
          ·
            refine ⟨237708812667519329724901451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158472541778346219816600967 237708812667519329724901451)
            ·
              refine ⟨356563219001278994587352177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237708812667519329724901451 356563219001278994587352177)
              ·
                refine ⟨267422414250959245940514133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356563219001278994587352177 267422414250959245940514133)
                ·
                  refine ⟨391732052125428582920675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 267422414250959245940514133 391732052125428582920675)
                  ·
                    rfl

theorem cell23_6866059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 11].length) (baseStart_6866059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866059 prefixEnd_6866059 := by exact prefixLift 6866059
  have htrace : WordTrace (prefixWord ++ tailWord_6866059) baseStart_6866059 baseEnd_6866059 := by
    simpa [prefixWord, tailWord_6866059, baseEnd_6866059] using wordTrace_append hprefix tailTrace_6866059
  have hstable : (prefixWord ++ tailWord_6866059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866059).length < 2 ^ (prefixWord ++ tailWord_6866059).sum := by decide
  have hdescent : baseEnd_6866059 < baseStart_6866059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866076 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 9]
def baseStart_6866076 : Nat := 118140960795 + 6866076 * 2 ^ 59
def prefixEnd_6866076 : Nat := 4983230072969 + 3 ^ 40 * 6866076 * 2
def baseEnd_6866076 : Nat := 391733022033331519974833

theorem tailTrace_6866076 : CollatzResearch.WordTrace tailWord_6866076 prefixEnd_6866076 391733022033331519974833 := by
  unfold tailWord_6866076
  simp only [CollatzResearch.WordTrace]
  refine ⟨125213182536693379633937041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166950910048924506178582721 125213182536693379633937041)
  ·
    refine ⟨93909886902520034725452781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125213182536693379633937041 93909886902520034725452781)
    ·
      refine ⟨35216207588445013022044793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93909886902520034725452781 35216207588445013022044793)
      ·
        refine ⟨26412155691333759766533595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35216207588445013022044793 26412155691333759766533595)
        ·
          refine ⟨39618233537000639649800393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26412155691333759766533595 39618233537000639649800393)
          ·
            refine ⟨29713675152750479737350295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39618233537000639649800393 29713675152750479737350295)
            ·
              refine ⟨44570512729125719606025443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29713675152750479737350295 44570512729125719606025443)
              ·
                refine ⟨66855769093688579409038165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44570512729125719606025443 66855769093688579409038165)
                ·
                  refine ⟨391733022033331519974833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66855769093688579409038165 391733022033331519974833)
                  ·
                    rfl

theorem cell23_6866076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_6866076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866076 prefixEnd_6866076 := by exact prefixLift 6866076
  have htrace : WordTrace (prefixWord ++ tailWord_6866076) baseStart_6866076 baseEnd_6866076 := by
    simpa [prefixWord, tailWord_6866076, baseEnd_6866076] using wordTrace_append hprefix tailTrace_6866076
  have hstable : (prefixWord ++ tailWord_6866076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866076).length < 2 ^ (prefixWord ++ tailWord_6866076).sum := by decide
  have hdescent : baseEnd_6866076 < baseStart_6866076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866106 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_6866106 : Nat := 118140960795 + 6866106 * 2 ^ 59
def prefixEnd_6866106 : Nat := 4983230072969 + 3 ^ 40 * 6866106 * 2
def baseEnd_6866106 : Nat := 1175204200906539520799453

theorem tailTrace_6866106 : CollatzResearch.WordTrace tailWord_6866106 prefixEnd_6866106 1175204200906539520799453 := by
  unfold tailWord_6866106
  simp only [CollatzResearch.WordTrace]
  refine ⟨62606864815819518597866543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166951639508852049594310781 62606864815819518597866543)
  ·
    refine ⟨93910297223729277896799815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62606864815819518597866543 93910297223729277896799815)
    ·
      refine ⟨140865445835593916845199723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93910297223729277896799815 140865445835593916845199723)
      ·
        refine ⟨211298168753390875267799585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140865445835593916845199723 211298168753390875267799585)
        ·
          refine ⟨158473626565043156450849689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211298168753390875267799585 158473626565043156450849689)
          ·
            refine ⟨118855219923782367338137267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158473626565043156450849689 118855219923782367338137267)
            ·
              refine ⟨178282829885673551007205901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118855219923782367338137267 178282829885673551007205901)
              ·
                refine ⟨66856061207127581627702213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178282829885673551007205901 66856061207127581627702213)
                ·
                  refine ⟨12535511476336421555194165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66856061207127581627702213 12535511476336421555194165)
                  ·
                    refine ⟨1175204200906539520799453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12535511476336421555194165 1175204200906539520799453)
                    ·
                      rfl

theorem cell23_6866106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_6866106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866106 prefixEnd_6866106 := by exact prefixLift 6866106
  have htrace : WordTrace (prefixWord ++ tailWord_6866106) baseStart_6866106 baseEnd_6866106 := by
    simpa [prefixWord, tailWord_6866106, baseEnd_6866106] using wordTrace_append hprefix tailTrace_6866106
  have hstable : (prefixWord ++ tailWord_6866106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866106).length < 2 ^ (prefixWord ++ tailWord_6866106).sum := by decide
  have hdescent : baseEnd_6866106 < baseStart_6866106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866110 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_6866110 : Nat := 118140960795 + 6866110 * 2 ^ 59
def prefixEnd_6866110 : Nat := 4983230072969 + 3 ^ 40 * 6866110 * 2
def baseEnd_6866110 : Nat := 391734961849137394083149

theorem tailTrace_6866110 : CollatzResearch.WordTrace tailWord_6866110 prefixEnd_6866110 391734961849137394083149 := by
  unfold tailWord_6866110
  simp only [CollatzResearch.WordTrace]
  refine ⟨31303450644407947884326473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166951736770175722049741189 31303450644407947884326473)
  ·
    refine ⟨23477587983305960913244855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31303450644407947884326473 23477587983305960913244855)
    ·
      refine ⟨35216381974958941369867283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23477587983305960913244855 35216381974958941369867283)
      ·
        refine ⟨52824572962438412054800925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35216381974958941369867283 52824572962438412054800925)
        ·
          refine ⟨19809214860914404520550347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52824572962438412054800925 19809214860914404520550347)
          ·
            refine ⟨29713822291371606780825521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19809214860914404520550347 29713822291371606780825521)
            ·
              refine ⟨22285366718528705085619141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29713822291371606780825521 22285366718528705085619141)
              ·
                refine ⟨4178506259724132203553589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22285366718528705085619141 4178506259724132203553589)
                ·
                  refine ⟨391734961849137394083149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4178506259724132203553589 391734961849137394083149)
                  ·
                    rfl

theorem cell23_6866110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_6866110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866110 prefixEnd_6866110 := by exact prefixLift 6866110
  have htrace : WordTrace (prefixWord ++ tailWord_6866110) baseStart_6866110 baseEnd_6866110 := by
    simpa [prefixWord, tailWord_6866110, baseEnd_6866110] using wordTrace_append hprefix tailTrace_6866110
  have hstable : (prefixWord ++ tailWord_6866110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866110).length < 2 ^ (prefixWord ++ tailWord_6866110).sum := by decide
  have hdescent : baseEnd_6866110 < baseStart_6866110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866143 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 6, 2]
def baseStart_6866143 : Nat := 118140960795 + 6866143 * 2 ^ 59
def prefixEnd_6866143 : Nat := 4983230072969 + 3 ^ 40 * 6866143 * 2
def baseEnd_6866143 : Nat := 3525631601503834917635689

theorem tailTrace_6866143 : CollatzResearch.WordTrace tailWord_6866143 prefixEnd_6866143 3525631601503834917635689 := by
  unfold tailWord_6866143
  simp only [CollatzResearch.WordTrace]
  refine ⟨250428808764144029710563083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166952539176096019807042055 250428808764144029710563083)
  ·
    refine ⟨375643213146216044565844625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250428808764144029710563083 375643213146216044565844625)
    ·
      refine ⟨281732409859662033424383469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375643213146216044565844625 281732409859662033424383469)
      ·
        refine ⟨105649653697373262534143801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281732409859662033424383469 105649653697373262534143801)
        ·
          refine ⟨79237240273029946900607851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105649653697373262534143801 79237240273029946900607851)
          ·
            refine ⟨118855860409544920350911777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79237240273029946900607851 118855860409544920350911777)
            ·
              refine ⟨89141895307158690263183833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118855860409544920350911777 89141895307158690263183833)
              ·
                refine ⟨66856421480369017697387875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89141895307158690263183833 66856421480369017697387875)
                ·
                  refine ⟨100284632220553526546081813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66856421480369017697387875 100284632220553526546081813)
                  ·
                    refine ⟨4700842135338446556847585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100284632220553526546081813 4700842135338446556847585)
                    ·
                      refine ⟨3525631601503834917635689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700842135338446556847585 3525631601503834917635689)
                      ·
                        rfl

theorem cell23_6866143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_6866143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866143 prefixEnd_6866143 := by exact prefixLift 6866143
  have htrace : WordTrace (prefixWord ++ tailWord_6866143) baseStart_6866143 baseEnd_6866143 := by
    simpa [prefixWord, tailWord_6866143, baseEnd_6866143] using wordTrace_append hprefix tailTrace_6866143
  have hstable : (prefixWord ++ tailWord_6866143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866143).length < 2 ^ (prefixWord ++ tailWord_6866143).sum := by decide
  have hdescent : baseEnd_6866143 < baseStart_6866143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866163 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3]
def baseStart_6866163 : Nat := 118140960795 + 6866163 * 2 ^ 59
def prefixEnd_6866163 : Nat := 4983230072969 + 3 ^ 40 * 6866163 * 2
def baseEnd_6866163 : Nat := 3525641871116924839385597

theorem tailTrace_6866163 : CollatzResearch.WordTrace tailWord_6866163 prefixEnd_6866163 3525641871116924839385597 := by
  unfold tailWord_6866163
  simp only [CollatzResearch.WordTrace]
  refine ⟨250429538224071573126291143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166953025482714382084194095 250429538224071573126291143)
  ·
    refine ⟨375644307336107359689436715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250429538224071573126291143 375644307336107359689436715)
    ·
      refine ⟨563466461004161039534155073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375644307336107359689436715 563466461004161039534155073)
      ·
        refine ⟨422599845753120779650616305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563466461004161039534155073 422599845753120779650616305)
        ·
          refine ⟨316949884314840584737962229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422599845753120779650616305 316949884314840584737962229)
          ·
            refine ⟨29714051654516304819183959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316949884314840584737962229 29714051654516304819183959)
            ·
              refine ⟨44571077481774457228775939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29714051654516304819183959 44571077481774457228775939)
              ·
                refine ⟨66856616222661685843163909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44571077481774457228775939 66856616222661685843163909)
                ·
                  refine ⟨12535615541749066095593233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66856616222661685843163909 12535615541749066095593233)
                  ·
                    refine ⟨9401711656311799571694925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12535615541749066095593233 9401711656311799571694925)
                    ·
                      refine ⟨3525641871116924839385597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9401711656311799571694925 3525641871116924839385597)
                      ·
                        rfl

theorem cell23_6866163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_6866163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866163 prefixEnd_6866163 := by exact prefixLift 6866163
  have htrace : WordTrace (prefixWord ++ tailWord_6866163) baseStart_6866163 baseEnd_6866163 := by
    simpa [prefixWord, tailWord_6866163, baseEnd_6866163] using wordTrace_append hprefix tailTrace_6866163
  have hstable : (prefixWord ++ tailWord_6866163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866163).length < 2 ^ (prefixWord ++ tailWord_6866163).sum := by decide
  have hdescent : baseEnd_6866163 < baseStart_6866163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866194 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6866194 : Nat := 118140960795 + 6866194 * 2 ^ 59
def prefixEnd_6866194 : Nat := 4983230072969 + 3 ^ 40 * 6866194 * 2
def baseEnd_6866194 : Nat := 3525657789017214218097955

theorem tailTrace_6866194 : CollatzResearch.WordTrace tailWord_6866194 prefixEnd_6866194 3525657789017214218097955 := by
  unfold tailWord_6866194
  simp only [CollatzResearch.WordTrace]
  refine ⟨62607667221739816355167409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166953779257972843613779757 62607667221739816355167409)
  ·
    refine ⟨46955750416304862266375557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62607667221739816355167409 46955750416304862266375557)
    ·
      refine ⟨8804203203057161674945417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46955750416304862266375557 8804203203057161674945417)
      ·
        refine ⟨6603152402292871256209063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8804203203057161674945417 6603152402292871256209063)
        ·
          refine ⟨9904728603439306884313595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603152402292871256209063 9904728603439306884313595)
          ·
            refine ⟨14857092905158960326470393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904728603439306884313595 14857092905158960326470393)
            ·
              refine ⟨11142819678869220244852795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14857092905158960326470393 11142819678869220244852795)
              ·
                refine ⟨16714229518303830367279193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142819678869220244852795 16714229518303830367279193)
                ·
                  refine ⟨12535672138727872775459395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16714229518303830367279193 12535672138727872775459395)
                  ·
                    refine ⟨18803508208091809163189093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12535672138727872775459395 18803508208091809163189093)
                    ·
                      refine ⟨3525657789017214218097955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18803508208091809163189093 3525657789017214218097955)
                      ·
                        rfl

theorem cell23_6866194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6866194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866194 prefixEnd_6866194 := by exact prefixLift 6866194
  have htrace : WordTrace (prefixWord ++ tailWord_6866194) baseStart_6866194 baseEnd_6866194 := by
    simpa [prefixWord, tailWord_6866194, baseEnd_6866194] using wordTrace_append hprefix tailTrace_6866194
  have hstable : (prefixWord ++ tailWord_6866194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866194).length < 2 ^ (prefixWord ++ tailWord_6866194).sum := by decide
  have hdescent : baseEnd_6866194 < baseStart_6866194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866221 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6866221 : Nat := 118140960795 + 6866221 * 2 ^ 59
def prefixEnd_6866221 : Nat := 4983230072969 + 3 ^ 40 * 6866221 * 2
def baseEnd_6866221 : Nat := 1175223884331628537486777

theorem tailTrace_6866221 : CollatzResearch.WordTrace tailWord_6866221 prefixEnd_6866221 1175223884331628537486777 := by
  unfold tailWord_6866221
  simp only [CollatzResearch.WordTrace]
  refine ⟨250431653657861449031902517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166954435771907632687935011 250431653657861449031902517)
  ·
    refine ⟨23477967530424510846740861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250431653657861449031902517 23477967530424510846740861)
    ·
      refine ⟨8804237823909191567527823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23477967530424510846740861 8804237823909191567527823)
      ·
        refine ⟨13206356735863787351291735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804237823909191567527823 13206356735863787351291735)
        ·
          refine ⟨19809535103795681026937603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206356735863787351291735 19809535103795681026937603)
          ·
            refine ⟨29714302655693521540406405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19809535103795681026937603 29714302655693521540406405)
            ·
              refine ⟨5571431747942535288826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29714302655693521540406405 5571431747942535288826201)
              ·
                refine ⟨4178573810956901466619651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571431747942535288826201 4178573810956901466619651)
                ·
                  refine ⟨6267860716435352199929477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178573810956901466619651 6267860716435352199929477)
                  ·
                    refine ⟨1175223884331628537486777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267860716435352199929477 1175223884331628537486777)
                    ·
                      rfl

theorem cell23_6866221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6866221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866221 prefixEnd_6866221 := by exact prefixLift 6866221
  have htrace : WordTrace (prefixWord ++ tailWord_6866221) baseStart_6866221 baseEnd_6866221 := by
    simpa [prefixWord, tailWord_6866221, baseEnd_6866221] using wordTrace_append hprefix tailTrace_6866221
  have hstable : (prefixWord ++ tailWord_6866221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866221).length < 2 ^ (prefixWord ++ tailWord_6866221).sum := by decide
  have hdescent : baseEnd_6866221 < baseStart_6866221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866243 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 6, 4]
def baseStart_6866243 : Nat := 118140960795 + 6866243 * 2 ^ 59
def prefixEnd_6866243 : Nat := 4983230072969 + 3 ^ 40 * 6866243 * 2
def baseEnd_6866243 : Nat := 1175227649856428175461743

theorem tailTrace_6866243 : CollatzResearch.WordTrace tailWord_6866243 prefixEnd_6866243 1175227649856428175461743 := by
  unfold tailWord_6866243
  simp only [CollatzResearch.WordTrace]
  refine ⟨250432456063781746789203383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166954970709187831192802255 250432456063781746789203383)
  ·
    refine ⟨375648684095672620183805075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250432456063781746789203383 375648684095672620183805075)
    ·
      refine ⟨563473026143508930275707613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375648684095672620183805075 563473026143508930275707613)
      ·
        refine ⟨211302384803815848853390355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563473026143508930275707613 211302384803815848853390355)
        ·
          refine ⟨316953577205723773280085533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211302384803815848853390355 316953577205723773280085533)
          ·
            refine ⟨118857591452146414980032075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316953577205723773280085533 118857591452146414980032075)
            ·
              refine ⟨178286387178219622470048113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118857591452146414980032075 178286387178219622470048113)
              ·
                refine ⟨133714790383664716852536085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178286387178219622470048113 133714790383664716852536085)
                ·
                  refine ⟨6267880799234283602462629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133714790383664716852536085 6267880799234283602462629)
                  ·
                    refine ⟨1175227649856428175461743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267880799234283602462629 1175227649856428175461743)
                    ·
                      rfl

theorem cell23_6866243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 4].length) (baseStart_6866243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866243 prefixEnd_6866243 := by exact prefixLift 6866243
  have htrace : WordTrace (prefixWord ++ tailWord_6866243) baseStart_6866243 baseEnd_6866243 := by
    simpa [prefixWord, tailWord_6866243, baseEnd_6866243] using wordTrace_append hprefix tailTrace_6866243
  have hstable : (prefixWord ++ tailWord_6866243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866243).length < 2 ^ (prefixWord ++ tailWord_6866243).sum := by decide
  have hdescent : baseEnd_6866243 < baseStart_6866243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866244 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6866244 : Nat := 118140960795 + 6866244 * 2 ^ 59
def prefixEnd_6866244 : Nat := 4983230072969 + 3 ^ 40 * 6866244 * 2
def baseEnd_6866244 : Nat := 3525683463049939022472725

theorem tailTrace_6866244 : CollatzResearch.WordTrace tailWord_6866244 prefixEnd_6866244 3525683463049939022472725 := by
  unfold tailWord_6866244
  simp only [CollatzResearch.WordTrace]
  refine ⟨125216246268389061979994893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166954995024518749306659857 125216246268389061979994893)
  ·
    refine ⟨46956092350645898242498085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125216246268389061979994893 46956092350645898242498085)
    ·
      refine ⟨8804267315746105920468391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46956092350645898242498085 8804267315746105920468391)
      ·
        refine ⟨13206400973619158880702587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804267315746105920468391 13206400973619158880702587)
        ·
          refine ⟨19809601460428738321053881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206400973619158880702587 19809601460428738321053881)
          ·
            refine ⟨14857201095321553740790411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19809601460428738321053881 14857201095321553740790411)
            ·
              refine ⟨22285801642982330611185617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857201095321553740790411 22285801642982330611185617)
              ·
                refine ⟨16714351232236747958389213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22285801642982330611185617 16714351232236747958389213)
                ·
                  refine ⟨6267881712088780484395955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16714351232236747958389213 6267881712088780484395955)
                  ·
                    refine ⟨9401822568133170726593933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6267881712088780484395955 9401822568133170726593933)
                    ·
                      refine ⟨3525683463049939022472725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9401822568133170726593933 3525683463049939022472725)
                      ·
                        rfl

theorem cell23_6866244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6866244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866244 prefixEnd_6866244 := by exact prefixLift 6866244
  have htrace : WordTrace (prefixWord ++ tailWord_6866244) baseStart_6866244 baseEnd_6866244 := by
    simpa [prefixWord, tailWord_6866244, baseEnd_6866244] using wordTrace_append hprefix tailTrace_6866244
  have hstable : (prefixWord ++ tailWord_6866244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866244).length < 2 ^ (prefixWord ++ tailWord_6866244).sum := by decide
  have hdescent : baseEnd_6866244 < baseStart_6866244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866260 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_6866260 : Nat := 118140960795 + 6866260 * 2 ^ 59
def prefixEnd_6866260 : Nat := 4983230072969 + 3 ^ 40 * 6866260 * 2
def baseEnd_6866260 : Nat := 1175230559580136986624217

theorem tailTrace_6866260 : CollatzResearch.WordTrace tailWord_6866260 prefixEnd_6866260 1175230559580136986624217 := by
  unfold tailWord_6866260
  simp only [CollatzResearch.WordTrace]
  refine ⟨125216538052360079346286117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166955384069813439128381489 125216538052360079346286117)
  ·
    refine ⟨23478100884817514877428647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125216538052360079346286117 23478100884817514877428647)
    ·
      refine ⟨35217151327226272316142971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23478100884817514877428647 35217151327226272316142971)
      ·
        refine ⟨52825726990839408474214457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35217151327226272316142971 52825726990839408474214457)
        ·
          refine ⟨39619295243129556355660843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52825726990839408474214457 39619295243129556355660843)
          ·
            refine ⟨59428942864694334533491265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39619295243129556355660843 59428942864694334533491265)
            ·
              refine ⟨44571707148520750900118449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59428942864694334533491265 44571707148520750900118449)
              ·
                refine ⟨33428780361390563175088837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44571707148520750900118449 33428780361390563175088837)
                ·
                  refine ⟨6267896317760730595329157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33428780361390563175088837 6267896317760730595329157)
                  ·
                    refine ⟨1175230559580136986624217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267896317760730595329157 1175230559580136986624217)
                    ·
                      rfl

theorem cell23_6866260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_6866260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866260 prefixEnd_6866260 := by exact prefixLift 6866260
  have htrace : WordTrace (prefixWord ++ tailWord_6866260) baseStart_6866260 baseEnd_6866260 := by
    simpa [prefixWord, tailWord_6866260, baseEnd_6866260] using wordTrace_append hprefix tailTrace_6866260
  have hstable : (prefixWord ++ tailWord_6866260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866260).length < 2 ^ (prefixWord ++ tailWord_6866260).sum := by decide
  have hdescent : baseEnd_6866260 < baseStart_6866260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866284 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_6866284 : Nat := 118140960795 + 6866284 * 2 ^ 59
def prefixEnd_6866284 : Nat := 4983230072969 + 3 ^ 40 * 6866284 * 2
def baseEnd_6866284 : Nat := 3525704002276118865972541

theorem tailTrace_6866284 : CollatzResearch.WordTrace tailWord_6866284 prefixEnd_6866284 3525704002276118865972541 := by
  unfold tailWord_6866284
  simp only [CollatzResearch.WordTrace]
  refine ⟨125216975728316605395722953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166955967637755473860963937 125216975728316605395722953)
  ·
    refine ⟨93912731796237454046792215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125216975728316605395722953 93912731796237454046792215)
    ·
      refine ⟨140869097694356181070188323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93912731796237454046792215 140869097694356181070188323)
      ·
        refine ⟨211303646541534271605282485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140869097694356181070188323 211303646541534271605282485)
        ·
          refine ⟨19809716863268837962995233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211303646541534271605282485 19809716863268837962995233)
          ·
            refine ⟨14857287647451628472246425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19809716863268837962995233 14857287647451628472246425)
            ·
              refine ⟨11142965735588721354184819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14857287647451628472246425 11142965735588721354184819)
              ·
                refine ⟨16714448603383082031277229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142965735588721354184819 16714448603383082031277229)
                ·
                  refine ⟨6267918226268655761728961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16714448603383082031277229 6267918226268655761728961)
                  ·
                    refine ⟨4700938669701491821296721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267918226268655761728961 4700938669701491821296721)
                    ·
                      refine ⟨3525704002276118865972541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700938669701491821296721 3525704002276118865972541)
                      ·
                        rfl

theorem cell23_6866284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_6866284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866284 prefixEnd_6866284 := by exact prefixLift 6866284
  have htrace : WordTrace (prefixWord ++ tailWord_6866284) baseStart_6866284 baseEnd_6866284 := by
    simpa [prefixWord, tailWord_6866284, baseEnd_6866284] using wordTrace_append hprefix tailTrace_6866284
  have hstable : (prefixWord ++ tailWord_6866284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866284).length < 2 ^ (prefixWord ++ tailWord_6866284).sum := by decide
  have hdescent : baseEnd_6866284 < baseStart_6866284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866361 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6866361 : Nat := 118140960795 + 6866361 * 2 ^ 59
def prefixEnd_6866361 : Nat := 4983230072969 + 3 ^ 40 * 6866361 * 2
def baseEnd_6866361 : Nat := 3525743540286515064709687

theorem tailTrace_6866361 : CollatzResearch.WordTrace tailWord_6866361 prefixEnd_6866361 3525743540286515064709687 := by
  unfold tailWord_6866361
  simp only [CollatzResearch.WordTrace]
  refine ⟨250436759877354252941998937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166957839918236168627999291 250436759877354252941998937)
  ·
    refine ⟨187827569908015689706499203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250436759877354252941998937 187827569908015689706499203)
    ·
      refine ⟨281741354862023534559748805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187827569908015689706499203 281741354862023534559748805)
      ·
        refine ⟨52826504036629412729952901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281741354862023534559748805 52826504036629412729952901)
        ·
          refine ⟨9904969506868014886866169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52826504036629412729952901 9904969506868014886866169)
          ·
            refine ⟨7428727130151011165149627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9904969506868014886866169 7428727130151011165149627)
            ·
              refine ⟨11143090695226516747724441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428727130151011165149627 11143090695226516747724441)
              ·
                refine ⟨8357318021419887560793331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11143090695226516747724441 8357318021419887560793331)
                ·
                  refine ⟨12535977032129831341189997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8357318021419887560793331 12535977032129831341189997)
                  ·
                    refine ⟨4700991387048686752946249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12535977032129831341189997 4700991387048686752946249)
                    ·
                      refine ⟨3525743540286515064709687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4700991387048686752946249 3525743540286515064709687)
                      ·
                        rfl

theorem cell23_6866361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6866361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866361 prefixEnd_6866361 := by exact prefixLift 6866361
  have htrace : WordTrace (prefixWord ++ tailWord_6866361) baseStart_6866361 baseEnd_6866361 := by
    simpa [prefixWord, tailWord_6866361, baseEnd_6866361] using wordTrace_append hprefix tailTrace_6866361
  have hstable : (prefixWord ++ tailWord_6866361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866361).length < 2 ^ (prefixWord ++ tailWord_6866361).sum := by decide
  have hdescent : baseEnd_6866361 < baseStart_6866361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866407 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6866407 : Nat := 118140960795 + 6866407 * 2 ^ 59
def prefixEnd_6866407 : Nat := 4983230072969 + 3 ^ 40 * 6866407 * 2
def baseEnd_6866407 : Nat := 3525767160396621884734475

theorem tailTrace_6866407 : CollatzResearch.WordTrace tailWord_6866407 prefixEnd_6866407 3525767160396621884734475 := by
  unfold tailWord_6866407
  simp only [CollatzResearch.WordTrace]
  refine ⟨250438437635187602798173475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166958958423458401865448983 250438437635187602798173475)
  ·
    refine ⟨375657656452781404197260213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250438437635187602798173475 375657656452781404197260213)
    ·
      refine ⟨35217905292448256643493145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 375657656452781404197260213 35217905292448256643493145)
      ·
        refine ⟨26413428969336192482619859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35217905292448256643493145 26413428969336192482619859)
        ·
          refine ⟨39620143454004288723929789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26413428969336192482619859 39620143454004288723929789)
          ·
            refine ⟨14857553795251608271473671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39620143454004288723929789 14857553795251608271473671)
            ·
              refine ⟨22286330692877412407210507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857553795251608271473671 22286330692877412407210507)
              ·
                refine ⟨33429496039316118610815761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22286330692877412407210507 33429496039316118610815761)
                ·
                  refine ⟨25072122029487088958111821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33429496039316118610815761 25072122029487088958111821)
                  ·
                    refine ⟨9402045761057658359291933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25072122029487088958111821 9402045761057658359291933)
                    ·
                      refine ⟨3525767160396621884734475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402045761057658359291933 3525767160396621884734475)
                      ·
                        rfl

theorem cell23_6866407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6866407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866407 prefixEnd_6866407 := by exact prefixLift 6866407
  have htrace : WordTrace (prefixWord ++ tailWord_6866407) baseStart_6866407 baseEnd_6866407 := by
    simpa [prefixWord, tailWord_6866407, baseEnd_6866407] using wordTrace_append hprefix tailTrace_6866407
  have hstable : (prefixWord ++ tailWord_6866407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866407).length < 2 ^ (prefixWord ++ tailWord_6866407).sum := by decide
  have hdescent : baseEnd_6866407 < baseStart_6866407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866423 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 10]
def baseStart_6866423 : Nat := 118140960795 + 6866423 * 2 ^ 59
def prefixEnd_6866423 : Nat := 4983230072969 + 3 ^ 40 * 6866423 * 2
def baseEnd_6866423 : Nat := 1175258458695697940711467

theorem tailTrace_6866423 : CollatzResearch.WordTrace tailWord_6866423 prefixEnd_6866423 1175258458695697940711467 := by
  unfold tailWord_6866423
  simp only [CollatzResearch.WordTrace]
  refine ⟨250439021203129637530755923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166959347468753091687170615 250439021203129637530755923)
  ·
    refine ⟨375658531804694456296133885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250439021203129637530755923 375658531804694456296133885)
    ·
      refine ⟨140871949426760421111050207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375658531804694456296133885 140871949426760421111050207)
      ·
        refine ⟨211307924140140631666575311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140871949426760421111050207 211307924140140631666575311)
        ·
          refine ⟨316961886210210947499862967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211307924140140631666575311 316961886210210947499862967)
          ·
            refine ⟨475442829315316421249794451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316961886210210947499862967 475442829315316421249794451)
            ·
              refine ⟨713164243972974631874691677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475442829315316421249794451 713164243972974631874691677)
              ·
                refine ⟨267436591489865486953009379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713164243972974631874691677 267436591489865486953009379)
                ·
                  refine ⟨401154887234798230429514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267436591489865486953009379 401154887234798230429514069)
                  ·
                    refine ⟨1175258458695697940711467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 401154887234798230429514069 1175258458695697940711467)
                    ·
                      rfl

theorem cell23_6866423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_6866423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866423 prefixEnd_6866423 := by exact prefixLift 6866423
  have htrace : WordTrace (prefixWord ++ tailWord_6866423) baseStart_6866423 baseEnd_6866423 := by
    simpa [prefixWord, tailWord_6866423, baseEnd_6866423] using wordTrace_append hprefix tailTrace_6866423
  have hstable : (prefixWord ++ tailWord_6866423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866423).length < 2 ^ (prefixWord ++ tailWord_6866423).sum := by decide
  have hdescent : baseEnd_6866423 < baseStart_6866423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866460 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6866460 : Nat := 118140960795 + 6866460 * 2 ^ 59
def prefixEnd_6866460 : Nat := 4983230072969 + 3 ^ 40 * 6866460 * 2
def baseEnd_6866460 : Nat := 3525794374871310177371731

theorem tailTrace_6866460 : CollatzResearch.WordTrace tailWord_6866460 prefixEnd_6866460 3525794374871310177371731 := by
  unfold tailWord_6866460
  simp only [CollatzResearch.WordTrace]
  refine ⟨125220185351997796424926417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166960247135997061899901889 125220185351997796424926417)
  ·
    refine ⟨93915139013998347318694813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125220185351997796424926417 93915139013998347318694813)
    ·
      refine ⟨35218177130249380244510555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93915139013998347318694813 35218177130249380244510555)
      ·
        refine ⟨52827265695374070366765833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35218177130249380244510555 52827265695374070366765833)
        ·
          refine ⟨39620449271530552775074375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52827265695374070366765833 39620449271530552775074375)
          ·
            refine ⟨59430673907295829162611563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39620449271530552775074375 59430673907295829162611563)
            ·
              refine ⟨89146010860943743743917345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59430673907295829162611563 89146010860943743743917345)
              ·
                refine ⟨66859508145707807807938009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89146010860943743743917345 66859508145707807807938009)
                ·
                  refine ⟨50144631109280855855953507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66859508145707807807938009 50144631109280855855953507)
                  ·
                    refine ⟨75216946663921283783930261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50144631109280855855953507 75216946663921283783930261)
                    ·
                      refine ⟨3525794374871310177371731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75216946663921283783930261 3525794374871310177371731)
                      ·
                        rfl

theorem cell23_6866460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6866460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866460 prefixEnd_6866460 := by exact prefixLift 6866460
  have htrace : WordTrace (prefixWord ++ tailWord_6866460) baseStart_6866460 baseEnd_6866460 := by
    simpa [prefixWord, tailWord_6866460, baseEnd_6866460] using wordTrace_append hprefix tailTrace_6866460
  have hstable : (prefixWord ++ tailWord_6866460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866460).length < 2 ^ (prefixWord ++ tailWord_6866460).sum := by decide
  have hdescent : baseEnd_6866460 < baseStart_6866460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866464 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6866464 : Nat := 118140960795 + 6866464 * 2 ^ 59
def prefixEnd_6866464 : Nat := 4983230072969 + 3 ^ 40 * 6866464 * 2
def baseEnd_6866464 : Nat := 3525796428793928161721713

theorem tailTrace_6866464 : CollatzResearch.WordTrace tailWord_6866464 prefixEnd_6866464 3525796428793928161721713 := by
  unfold tailWord_6866464
  simp only [CollatzResearch.WordTrace]
  refine ⟨125220258297990550766499223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166960344397320734355332297 125220258297990550766499223)
  ·
    refine ⟨187830387446985826149748835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125220258297990550766499223 187830387446985826149748835)
    ·
      refine ⟨281745581170478739224623253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187830387446985826149748835 281745581170478739224623253)
      ·
        refine ⟨13206824117366190901154215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281745581170478739224623253 13206824117366190901154215)
        ·
          refine ⟨19810236176049286351731323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206824117366190901154215 19810236176049286351731323)
          ·
            refine ⟨29715354264073929527596985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19810236176049286351731323 29715354264073929527596985)
            ·
              refine ⟨22286515698055447145697739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29715354264073929527596985 22286515698055447145697739)
              ·
                refine ⟨33429773547083170718546609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22286515698055447145697739 33429773547083170718546609)
                ·
                  refine ⟨25072330160312378038909957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33429773547083170718546609 25072330160312378038909957)
                  ·
                    refine ⟨4701061905058570882295617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25072330160312378038909957 4701061905058570882295617)
                    ·
                      refine ⟨3525796428793928161721713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701061905058570882295617 3525796428793928161721713)
                      ·
                        rfl

theorem cell23_6866464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6866464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866464 prefixEnd_6866464 := by exact prefixLift 6866464
  have htrace : WordTrace (prefixWord ++ tailWord_6866464) baseStart_6866464 baseEnd_6866464 := by
    simpa [prefixWord, tailWord_6866464, baseEnd_6866464] using wordTrace_append hprefix tailTrace_6866464
  have hstable : (prefixWord ++ tailWord_6866464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866464).length < 2 ^ (prefixWord ++ tailWord_6866464).sum := by decide
  have hdescent : baseEnd_6866464 < baseStart_6866464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866480 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_6866480 : Nat := 118140960795 + 6866480 * 2 ^ 59
def prefixEnd_6866480 : Nat := 4983230072969 + 3 ^ 40 * 6866480 * 2
def baseEnd_6866480 : Nat := 3525804644484400099121639

theorem tailTrace_6866480 : CollatzResearch.WordTrace tailWord_6866480 prefixEnd_6866480 3525804644484400099121639 := by
  unfold tailWord_6866480
  simp only [CollatzResearch.WordTrace]
  refine ⟨125220550081961568132790447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166960733442615424177053929 125220550081961568132790447)
  ·
    refine ⟨187830825122942352199185671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125220550081961568132790447 187830825122942352199185671)
    ·
      refine ⟨281746237684413528298778507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187830825122942352199185671 281746237684413528298778507)
      ·
        refine ⟨422619356526620292448167761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281746237684413528298778507 422619356526620292448167761)
        ·
          refine ⟨316964517394965219336125821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422619356526620292448167761 316964517394965219336125821)
          ·
            refine ⟨118861694023111957251047183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316964517394965219336125821 118861694023111957251047183)
            ·
              refine ⟨178292541034667935876570775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118861694023111957251047183 178292541034667935876570775)
              ·
                refine ⟨267438811552001903814856163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178292541034667935876570775 267438811552001903814856163)
                ·
                  refine ⟨401158217328002855722284245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267438811552001903814856163 401158217328002855722284245)
                  ·
                    refine ⟨9402145718625066930991037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 401158217328002855722284245 9402145718625066930991037)
                    ·
                      refine ⟨3525804644484400099121639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402145718625066930991037 3525804644484400099121639)
                      ·
                        rfl

theorem cell23_6866480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_6866480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866480 prefixEnd_6866480 := by exact prefixLift 6866480
  have htrace : WordTrace (prefixWord ++ tailWord_6866480) baseStart_6866480 baseEnd_6866480 := by
    simpa [prefixWord, tailWord_6866480, baseEnd_6866480] using wordTrace_append hprefix tailTrace_6866480
  have hstable : (prefixWord ++ tailWord_6866480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866480).length < 2 ^ (prefixWord ++ tailWord_6866480).sum := by decide
  have hdescent : baseEnd_6866480 < baseStart_6866480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866510 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6866510 : Nat := 118140960795 + 6866510 * 2 ^ 59
def prefixEnd_6866510 : Nat := 4983230072969 + 3 ^ 40 * 6866510 * 2
def baseEnd_6866510 : Nat := 3525820048904034981746501

theorem tailTrace_6866510 : CollatzResearch.WordTrace tailWord_6866510 prefixEnd_6866510 3525820048904034981746501 := by
  unfold tailWord_6866510
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305274294226806423646623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166961462902542967592781989 31305274294226806423646623)
  ·
    refine ⟨46957911441340209635469935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31305274294226806423646623 46957911441340209635469935)
    ·
      refine ⟨70436867162010314453204903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46957911441340209635469935 70436867162010314453204903)
      ·
        refine ⟨105655300743015471679807355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70436867162010314453204903 105655300743015471679807355)
        ·
          refine ⟨158482951114523207519711033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105655300743015471679807355 158482951114523207519711033)
          ·
            refine ⟨118862213335892405639783275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158482951114523207519711033 118862213335892405639783275)
            ·
              refine ⟨178293320003838608459674913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118862213335892405639783275 178293320003838608459674913)
              ·
                refine ⟨133719990002878956344756185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178293320003838608459674913 133719990002878956344756185)
                ·
                  refine ⟨100289992502159217258567139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133719990002878956344756185 100289992502159217258567139)
                  ·
                    refine ⟨150434988753238825887850709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100289992502159217258567139 150434988753238825887850709)
                    ·
                      refine ⟨3525820048904034981746501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150434988753238825887850709 3525820048904034981746501)
                      ·
                        rfl

theorem cell23_6866510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6866510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866510 prefixEnd_6866510 := by exact prefixLift 6866510
  have htrace : WordTrace (prefixWord ++ tailWord_6866510) baseStart_6866510 baseEnd_6866510 := by
    simpa [prefixWord, tailWord_6866510, baseEnd_6866510] using wordTrace_append hprefix tailTrace_6866510
  have hstable : (prefixWord ++ tailWord_6866510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866510).length < 2 ^ (prefixWord ++ tailWord_6866510).sum := by decide
  have hdescent : baseEnd_6866510 < baseStart_6866510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866520 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_6866520 : Nat := 118140960795 + 6866520 * 2 ^ 59
def prefixEnd_6866520 : Nat := 4983230072969 + 3 ^ 40 * 6866520 * 2
def baseEnd_6866520 : Nat := 3525825183710579942621455

theorem tailTrace_6866520 : CollatzResearch.WordTrace tailWord_6866520 prefixEnd_6866520 3525825183710579942621455 := by
  unfold tailWord_6866520
  simp only [CollatzResearch.WordTrace]
  refine ⟨125221279541889111548518507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166961706055852148731358009 125221279541889111548518507)
  ·
    refine ⟨187831919312833667322777761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125221279541889111548518507 187831919312833667322777761)
    ·
      refine ⟨140873939484625250492083321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187831919312833667322777761 140873939484625250492083321)
      ·
        refine ⟨105655454613468937869062491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140873939484625250492083321 105655454613468937869062491)
        ·
          refine ⟨158483181920203406803593737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105655454613468937869062491 158483181920203406803593737)
          ·
            refine ⟨118862386440152555102695303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158483181920203406803593737 118862386440152555102695303)
            ·
              refine ⟨178293579660228832654042955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118862386440152555102695303 178293579660228832654042955)
              ·
                refine ⟨267440369490343248981064433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178293579660228832654042955 267440369490343248981064433)
                ·
                  refine ⟨200580277117757436735798325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267440369490343248981064433 200580277117757436735798325)
                  ·
                    refine ⟨18804400979789759693981093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200580277117757436735798325 18804400979789759693981093)
                    ·
                      refine ⟨3525825183710579942621455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18804400979789759693981093 3525825183710579942621455)
                      ·
                        rfl

theorem cell23_6866520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_6866520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866520 prefixEnd_6866520 := by exact prefixLift 6866520
  have htrace : WordTrace (prefixWord ++ tailWord_6866520) baseStart_6866520 baseEnd_6866520 := by
    simpa [prefixWord, tailWord_6866520, baseEnd_6866520] using wordTrace_append hprefix tailTrace_6866520
  have hstable : (prefixWord ++ tailWord_6866520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866520).length < 2 ^ (prefixWord ++ tailWord_6866520).sum := by decide
  have hdescent : baseEnd_6866520 < baseStart_6866520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866537 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 6, 2]
def baseStart_6866537 : Nat := 118140960795 + 6866537 * 2 ^ 59
def prefixEnd_6866537 : Nat := 4983230072969 + 3 ^ 40 * 6866537 * 2
def baseEnd_6866537 : Nat := 3525833912881706376108877

theorem tailTrace_6866537 : CollatzResearch.WordTrace tailWord_6866537 prefixEnd_6866537 3525833912881706376108877 := by
  unfold tailWord_6866537
  simp only [CollatzResearch.WordTrace]
  refine ⟨250443179124716635000405865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166962119416477756666937243 250443179124716635000405865)
  ·
    refine ⟨187832384343537476250304399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250443179124716635000405865 187832384343537476250304399)
    ·
      refine ⟨281748576515306214375456599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187832384343537476250304399 281748576515306214375456599)
      ·
        refine ⟨422622864772959321563184899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281748576515306214375456599 422622864772959321563184899)
        ·
          refine ⟨633934297159438982344777349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422622864772959321563184899 633934297159438982344777349)
          ·
            refine ⟨118862680717394809189645753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 633934297159438982344777349 118862680717394809189645753)
            ·
              refine ⟨89147010538046106892234315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118862680717394809189645753 89147010538046106892234315)
              ·
                refine ⟨133720515807069160338351473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89147010538046106892234315 133720515807069160338351473)
                ·
                  refine ⟨100290386855301870253763605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133720515807069160338351473 100290386855301870253763605)
                  ·
                    refine ⟨4701111883842275168145169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100290386855301870253763605 4701111883842275168145169)
                    ·
                      refine ⟨3525833912881706376108877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701111883842275168145169 3525833912881706376108877)
                      ·
                        rfl

theorem cell23_6866537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6, 2].length) (baseStart_6866537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866537 prefixEnd_6866537 := by exact prefixLift 6866537
  have htrace : WordTrace (prefixWord ++ tailWord_6866537) baseStart_6866537 baseEnd_6866537 := by
    simpa [prefixWord, tailWord_6866537, baseEnd_6866537] using wordTrace_append hprefix tailTrace_6866537
  have hstable : (prefixWord ++ tailWord_6866537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866537).length < 2 ^ (prefixWord ++ tailWord_6866537).sum := by decide
  have hdescent : baseEnd_6866537 < baseStart_6866537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866554 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_6866554 : Nat := 118140960795 + 6866554 * 2 ^ 59
def prefixEnd_6866554 : Nat := 4983230072969 + 3 ^ 40 * 6866554 * 2
def baseEnd_6866554 : Nat := 3525842642052832809596299

theorem tailTrace_6866554 : CollatzResearch.WordTrace tailWord_6866554 prefixEnd_6866554 3525842642052832809596299 := by
  unfold tailWord_6866554
  simp only [CollatzResearch.WordTrace]
  refine ⟨62610949791413761725943679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166962532777103364602516477 62610949791413761725943679)
  ·
    refine ⟨93916424687120642588915519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62610949791413761725943679 93916424687120642588915519)
    ·
      refine ⟨140874637030680963883373279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93916424687120642588915519 140874637030680963883373279)
      ·
        refine ⟨211311955546021445825059919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140874637030680963883373279 211311955546021445825059919)
        ·
          refine ⟨316967933319032168737589879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211311955546021445825059919 316967933319032168737589879)
          ·
            refine ⟨475451899978548253106384819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316967933319032168737589879 475451899978548253106384819)
            ·
              refine ⟨713177849967822379659577229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475451899978548253106384819 713177849967822379659577229)
              ·
                refine ⟨267441693737933392372341461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713177849967822379659577229 267441693737933392372341461)
                ·
                  refine ⟨6268164696982813883726753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 267441693737933392372341461 6268164696982813883726753)
                  ·
                    refine ⟨4701123522737110412795065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268164696982813883726753 4701123522737110412795065)
                    ·
                      refine ⟨3525842642052832809596299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701123522737110412795065 3525842642052832809596299)
                      ·
                        rfl

theorem cell23_6866554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_6866554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866554 prefixEnd_6866554 := by exact prefixLift 6866554
  have htrace : WordTrace (prefixWord ++ tailWord_6866554) baseStart_6866554 baseEnd_6866554 := by
    simpa [prefixWord, tailWord_6866554, baseEnd_6866554] using wordTrace_append hprefix tailTrace_6866554
  have hstable : (prefixWord ++ tailWord_6866554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866554).length < 2 ^ (prefixWord ++ tailWord_6866554).sum := by decide
  have hdescent : baseEnd_6866554 < baseStart_6866554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866574 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6866574 : Nat := 118140960795 + 6866574 * 2 ^ 59
def prefixEnd_6866574 : Nat := 4983230072969 + 3 ^ 40 * 6866574 * 2
def baseEnd_6866574 : Nat := 3525852911665922731346207

theorem tailTrace_6866574 : CollatzResearch.WordTrace tailWord_6866574 prefixEnd_6866574 3525852911665922731346207 := by
  unfold tailWord_6866574
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305566078197823789937847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166963019083721726879668517 31305566078197823789937847)
  ·
    refine ⟨46958349117296735684906771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31305566078197823789937847 46958349117296735684906771)
    ·
      refine ⟨70437523675945103527360157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46958349117296735684906771 70437523675945103527360157)
      ·
        refine ⟨26414071378479413822760059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70437523675945103527360157 26414071378479413822760059)
        ·
          refine ⟨39621107067719120734140089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26414071378479413822760059 39621107067719120734140089)
          ·
            refine ⟨29715830300789340550605067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39621107067719120734140089 29715830300789340550605067)
            ·
              refine ⟨44573745451184010825907601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29715830300789340550605067 44573745451184010825907601)
              ·
                refine ⟨33430309088388008119430701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44573745451184010825907601 33430309088388008119430701)
                ·
                  refine ⟨12536365908145503044786513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33430309088388008119430701 12536365908145503044786513)
                  ·
                    refine ⟨9402274431109127283589885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12536365908145503044786513 9402274431109127283589885)
                    ·
                      refine ⟨3525852911665922731346207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402274431109127283589885 3525852911665922731346207)
                      ·
                        rfl

theorem cell23_6866574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6866574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866574 prefixEnd_6866574 := by exact prefixLift 6866574
  have htrace : WordTrace (prefixWord ++ tailWord_6866574) baseStart_6866574 baseEnd_6866574 := by
    simpa [prefixWord, tailWord_6866574, baseEnd_6866574] using wordTrace_append hprefix tailTrace_6866574
  have hstable : (prefixWord ++ tailWord_6866574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866574).length < 2 ^ (prefixWord ++ tailWord_6866574).sum := by decide
  have hdescent : baseEnd_6866574 < baseStart_6866574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866584 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6866584 : Nat := 118140960795 + 6866584 * 2 ^ 59
def prefixEnd_6866584 : Nat := 4983230072969 + 3 ^ 40 * 6866584 * 2
def baseEnd_6866584 : Nat := 3525858046472467692221161

theorem tailTrace_6866584 : CollatzResearch.WordTrace tailWord_6866584 prefixEnd_6866584 3525858046472467692221161 := by
  unfold tailWord_6866584
  simp only [CollatzResearch.WordTrace]
  refine ⟨125222446677773181013683403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166963262237030908018244537 125222446677773181013683403)
  ·
    refine ⟨187833670016659771520525105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125222446677773181013683403 187833670016659771520525105)
    ·
      refine ⟨140875252512494828640393829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187833670016659771520525105 140875252512494828640393829)
      ·
        refine ⟨26414109846092780370073843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140875252512494828640393829 26414109846092780370073843)
        ·
          refine ⟨39621164769139170555110765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26414109846092780370073843 39621164769139170555110765)
          ·
            refine ⟨14857936788427188958166537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39621164769139170555110765 14857936788427188958166537)
            ·
              refine ⟨11143452591320391718624903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14857936788427188958166537 11143452591320391718624903)
              ·
                refine ⟨16715178886980587577937355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11143452591320391718624903 16715178886980587577937355)
                ·
                  refine ⟨25072768330470881366906033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16715178886980587577937355 25072768330470881366906033)
                  ·
                    refine ⟨18804576247853161025179525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25072768330470881366906033 18804576247853161025179525)
                    ·
                      refine ⟨3525858046472467692221161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18804576247853161025179525 3525858046472467692221161)
                      ·
                        rfl

theorem cell23_6866584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6866584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866584 prefixEnd_6866584 := by exact prefixLift 6866584
  have htrace : WordTrace (prefixWord ++ tailWord_6866584) baseStart_6866584 baseEnd_6866584 := by
    simpa [prefixWord, tailWord_6866584, baseEnd_6866584] using wordTrace_append hprefix tailTrace_6866584
  have hstable : (prefixWord ++ tailWord_6866584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866584).length < 2 ^ (prefixWord ++ tailWord_6866584).sum := by decide
  have hdescent : baseEnd_6866584 < baseStart_6866584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866588 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6866588 : Nat := 118140960795 + 6866588 * 2 ^ 59
def prefixEnd_6866588 : Nat := 4983230072969 + 3 ^ 40 * 6866588 * 2
def baseEnd_6866588 : Nat := 3525860100395085676571143

theorem tailTrace_6866588 : CollatzResearch.WordTrace tailWord_6866588 prefixEnd_6866588 3525860100395085676571143 := by
  unfold tailWord_6866588
  simp only [CollatzResearch.WordTrace]
  refine ⟨125222519623765935355256209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166963359498354580473674945 125222519623765935355256209)
  ·
    refine ⟨93916889717824451516442157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125222519623765935355256209 93916889717824451516442157)
    ·
      refine ⟨35218833644184169318665809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93916889717824451516442157 35218833644184169318665809)
      ·
        refine ⟨26414125233138126988999357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35218833644184169318665809 26414125233138126988999357)
        ·
          refine ⟨9905296962426797620874759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26414125233138126988999357 9905296962426797620874759)
          ·
            refine ⟨14857945443640196431312139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905296962426797620874759 14857945443640196431312139)
            ·
              refine ⟨22286918165460294646968209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857945443640196431312139 22286918165460294646968209)
              ·
                refine ⟨16715188624095220985226157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22286918165460294646968209 16715188624095220985226157)
                ·
                  refine ⟨6268195734035707869459809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16715188624095220985226157 6268195734035707869459809)
                  ·
                    refine ⟨4701146800526780902094857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268195734035707869459809 4701146800526780902094857)
                    ·
                      refine ⟨3525860100395085676571143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701146800526780902094857 3525860100395085676571143)
                      ·
                        rfl

theorem cell23_6866588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6866588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866588 prefixEnd_6866588 := by exact prefixLift 6866588
  have htrace : WordTrace (prefixWord ++ tailWord_6866588) baseStart_6866588 baseEnd_6866588 := by
    simpa [prefixWord, tailWord_6866588, baseEnd_6866588] using wordTrace_append hprefix tailTrace_6866588
  have hstable : (prefixWord ++ tailWord_6866588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866588).length < 2 ^ (prefixWord ++ tailWord_6866588).sum := by decide
  have hdescent : baseEnd_6866588 < baseStart_6866588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866605 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_6866605 : Nat := 118140960795 + 6866605 * 2 ^ 59
def prefixEnd_6866605 : Nat := 4983230072969 + 3 ^ 40 * 6866605 * 2
def baseEnd_6866605 : Nat := 3525868829566212110058565

theorem tailTrace_6866605 : CollatzResearch.WordTrace tailWord_6866605 prefixEnd_6866605 3525868829566212110058565 := by
  unfold tailWord_6866605
  simp only [CollatzResearch.WordTrace]
  refine ⟨250445659288470282613881269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166963772858980188409254179 250445659288470282613881269)
  ·
    refine ⟨23479280558294088995051369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250445659288470282613881269 23479280558294088995051369)
    ·
      refine ⟨17609460418720566746288527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23479280558294088995051369 17609460418720566746288527)
      ·
        refine ⟨26414190628080850119432791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17609460418720566746288527 26414190628080850119432791)
        ·
          refine ⟨39621285942121275179149187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26414190628080850119432791 39621285942121275179149187)
          ·
            refine ⟨59431928913181912768723781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39621285942121275179149187 59431928913181912768723781)
            ·
              refine ⟨11143486671221608644135709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59431928913181912768723781 11143486671221608644135709)
              ·
                refine ⟨4178807501708103241550891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143486671221608644135709 4178807501708103241550891)
                ·
                  refine ⟨6268211252562154862326337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178807501708103241550891 6268211252562154862326337)
                  ·
                    refine ⟨4701158439421616146744753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268211252562154862326337 4701158439421616146744753)
                    ·
                      refine ⟨3525868829566212110058565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701158439421616146744753 3525868829566212110058565)
                      ·
                        rfl

theorem cell23_6866605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_6866605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866605 prefixEnd_6866605 := by exact prefixLift 6866605
  have htrace : WordTrace (prefixWord ++ tailWord_6866605) baseStart_6866605 baseEnd_6866605 := by
    simpa [prefixWord, tailWord_6866605, baseEnd_6866605] using wordTrace_append hprefix tailTrace_6866605
  have hstable : (prefixWord ++ tailWord_6866605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866605).length < 2 ^ (prefixWord ++ tailWord_6866605).sum := by decide
  have hdescent : baseEnd_6866605 < baseStart_6866605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866638 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_6866638 : Nat := 118140960795 + 6866638 * 2 ^ 59
def prefixEnd_6866638 : Nat := 4983230072969 + 3 ^ 40 * 6866638 * 2
def baseEnd_6866638 : Nat := 3525885774427810480945913

theorem tailTrace_6866638 : CollatzResearch.WordTrace tailWord_6866638 prefixEnd_6866638 3525885774427810480945913 := by
  unfold tailWord_6866638
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305857862168841156229071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166964575264900486166555045 31305857862168841156229071)
  ·
    refine ⟨46958786793253261734343607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31305857862168841156229071 46958786793253261734343607)
    ·
      refine ⟨70438180189879892601515411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46958786793253261734343607 70438180189879892601515411)
      ·
        refine ⟨105657270284819838902273117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70438180189879892601515411 105657270284819838902273117)
        ·
          refine ⟨39621476356807439588352419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105657270284819838902273117 39621476356807439588352419)
          ·
            refine ⟨59432214535211159382528629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39621476356807439588352419 59432214535211159382528629)
            ·
              refine ⟨5571770112676046192112059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59432214535211159382528629 5571770112676046192112059)
              ·
                refine ⟨8357655169014069288168089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571770112676046192112059 8357655169014069288168089)
                ·
                  refine ⟨6268241376760551966126067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357655169014069288168089 6268241376760551966126067)
                  ·
                    refine ⟨9402362065140827949189101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6268241376760551966126067 9402362065140827949189101)
                    ·
                      refine ⟨3525885774427810480945913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402362065140827949189101 3525885774427810480945913)
                      ·
                        rfl

theorem cell23_6866638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_6866638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866638 prefixEnd_6866638 := by exact prefixLift 6866638
  have htrace : WordTrace (prefixWord ++ tailWord_6866638) baseStart_6866638 baseEnd_6866638 := by
    simpa [prefixWord, tailWord_6866638, baseEnd_6866638] using wordTrace_append hprefix tailTrace_6866638
  have hstable : (prefixWord ++ tailWord_6866638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866638).length < 2 ^ (prefixWord ++ tailWord_6866638).sum := by decide
  have hdescent : baseEnd_6866638 < baseStart_6866638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866647 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_6866647 : Nat := 118140960795 + 6866647 * 2 ^ 59
def prefixEnd_6866647 : Nat := 4983230072969 + 3 ^ 40 * 6866647 * 2
def baseEnd_6866647 : Nat := 3525890395753700945733371

theorem tailTrace_6866647 : CollatzResearch.WordTrace tailWord_6866647 prefixEnd_6866647 3525890395753700945733371 := by
  unfold tailWord_6866647
  simp only [CollatzResearch.WordTrace]
  refine ⟨250447191154318123786910195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166964794102878749191273463 250447191154318123786910195)
  ·
    refine ⟨375670786731477185680365293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250447191154318123786910195 375670786731477185680365293)
    ·
      refine ⟨140876545024303944630136985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375670786731477185680365293 140876545024303944630136985)
      ·
        refine ⟨105657408768227958472602739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140876545024303944630136985 105657408768227958472602739)
        ·
          refine ⟨158486113152341937708904109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105657408768227958472602739 158486113152341937708904109)
          ·
            refine ⟨59432292432128226640839041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158486113152341937708904109 59432292432128226640839041)
            ·
              refine ⟨44574219324096169980629281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59432292432128226640839041 44574219324096169980629281)
              ·
                refine ⟨33430664493072127485471961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44574219324096169980629281 33430664493072127485471961)
                ·
                  refine ⟨25072998369804095614103971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33430664493072127485471961 25072998369804095614103971)
                  ·
                    refine ⟨37609497554706143421155957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25072998369804095614103971 37609497554706143421155957)
                    ·
                      refine ⟨3525890395753700945733371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37609497554706143421155957 3525890395753700945733371)
                      ·
                        rfl

theorem cell23_6866647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_6866647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866647 prefixEnd_6866647 := by exact prefixLift 6866647
  have htrace : WordTrace (prefixWord ++ tailWord_6866647) baseStart_6866647 baseEnd_6866647 := by
    simpa [prefixWord, tailWord_6866647, baseEnd_6866647] using wordTrace_append hprefix tailTrace_6866647
  have hstable : (prefixWord ++ tailWord_6866647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866647).length < 2 ^ (prefixWord ++ tailWord_6866647).sum := by decide
  have hdescent : baseEnd_6866647 < baseStart_6866647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866661 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6866661 : Nat := 118140960795 + 6866661 * 2 ^ 59
def prefixEnd_6866661 : Nat := 4983230072969 + 3 ^ 40 * 6866661 * 2
def baseEnd_6866661 : Nat := 3525897584482863890958307

theorem tailTrace_6866661 : CollatzResearch.WordTrace tailWord_6866661 prefixEnd_6866661 3525897584482863890958307 := by
  unfold tailWord_6866661
  simp only [CollatzResearch.WordTrace]
  refine ⟨250447701776267404177919837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166965134517511602785279891 250447701776267404177919837)
  ·
    refine ⟨93917888166100276566719939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250447701776267404177919837 93917888166100276566719939)
    ·
      refine ⟨140876832249150414850079909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93917888166100276566719939 140876832249150414850079909)
      ·
        refine ⟨26414406046715702784389983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140876832249150414850079909 26414406046715702784389983)
        ·
          refine ⟨39621609070073554176584975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26414406046715702784389983 39621609070073554176584975)
          ·
            refine ⟨59432413605110331264877463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39621609070073554176584975 59432413605110331264877463)
            ·
              refine ⟨89148620407665496897316195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59432413605110331264877463 89148620407665496897316195)
              ·
                refine ⟨133722930611498245345974293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89148620407665496897316195 133722930611498245345974293)
                ·
                  refine ⟨6268262372413980250592545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133722930611498245345974293 6268262372413980250592545)
                  ·
                    refine ⟨4701196779310485187944409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268262372413980250592545 4701196779310485187944409)
                    ·
                      refine ⟨3525897584482863890958307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701196779310485187944409 3525897584482863890958307)
                      ·
                        rfl

theorem cell23_6866661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6866661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866661 prefixEnd_6866661 := by exact prefixLift 6866661
  have htrace : WordTrace (prefixWord ++ tailWord_6866661) baseStart_6866661 baseEnd_6866661 := by
    simpa [prefixWord, tailWord_6866661, baseEnd_6866661] using wordTrace_append hprefix tailTrace_6866661
  have hstable : (prefixWord ++ tailWord_6866661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866661).length < 2 ^ (prefixWord ++ tailWord_6866661).sum := by decide
  have hdescent : baseEnd_6866661 < baseStart_6866661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866664 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6866664 : Nat := 118140960795 + 6866664 * 2 ^ 59
def prefixEnd_6866664 : Nat := 4983230072969 + 3 ^ 40 * 6866664 * 2
def baseEnd_6866664 : Nat := 3525899124924827379220793

theorem tailTrace_6866664 : CollatzResearch.WordTrace tailWord_6866664 prefixEnd_6866664 3525899124924827379220793 := by
  unfold tailWord_6866664
  simp only [CollatzResearch.WordTrace]
  refine ⟨125223905597628267845139523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166965207463504357126852697 125223905597628267845139523)
  ·
    refine ⟨187835858396442401767709285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125223905597628267845139523 187835858396442401767709285)
    ·
      refine ⟨35219223449332950331445491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187835858396442401767709285 35219223449332950331445491)
      ·
        refine ⟨52828835173999425497168237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35219223449332950331445491 52828835173999425497168237)
        ·
          refine ⟨19810813190249784561438089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52828835173999425497168237 19810813190249784561438089)
          ·
            refine ⟨14858109892687338421078567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810813190249784561438089 14858109892687338421078567)
            ·
              refine ⟨22287164839031007631617851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858109892687338421078567 22287164839031007631617851)
              ·
                refine ⟨33430747258546511447426777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22287164839031007631617851 33430747258546511447426777)
                ·
                  refine ⟨25073060443909883585570083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33430747258546511447426777 25073060443909883585570083)
                  ·
                    refine ⟨37609590665864825378355125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25073060443909883585570083 37609590665864825378355125)
                    ·
                      refine ⟨3525899124924827379220793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37609590665864825378355125 3525899124924827379220793)
                      ·
                        rfl

theorem cell23_6866664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6866664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866664 prefixEnd_6866664 := by exact prefixLift 6866664
  have htrace : WordTrace (prefixWord ++ tailWord_6866664) baseStart_6866664 baseEnd_6866664 := by
    simpa [prefixWord, tailWord_6866664, baseEnd_6866664] using wordTrace_append hprefix tailTrace_6866664
  have hstable : (prefixWord ++ tailWord_6866664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866664).length < 2 ^ (prefixWord ++ tailWord_6866664).sum := by decide
  have hdescent : baseEnd_6866664 < baseStart_6866664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866678 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6866678 : Nat := 118140960795 + 6866678 * 2 ^ 59
def prefixEnd_6866678 : Nat := 4983230072969 + 3 ^ 40 * 6866678 * 2
def baseEnd_6866678 : Nat := 3525906313653990324445729

theorem tailTrace_6866678 : CollatzResearch.WordTrace tailWord_6866678 prefixEnd_6866678 3525906313653990324445729 := by
  unfold tailWord_6866678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653020113575363505080543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166965547878137210720859125 15653020113575363505080543)
  ·
    refine ⟨23479530170363045257620815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15653020113575363505080543 23479530170363045257620815)
    ·
      refine ⟨35219295255544567886431223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23479530170363045257620815 35219295255544567886431223)
      ·
        refine ⟨52828942883316851829646835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35219295255544567886431223 52828942883316851829646835)
        ·
          refine ⟨79243414324975277744470253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52828942883316851829646835 79243414324975277744470253)
          ·
            refine ⟨29716280371865729154176345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79243414324975277744470253 29716280371865729154176345)
            ·
              refine ⟨22287210278899296865632259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29716280371865729154176345 22287210278899296865632259)
              ·
                refine ⟨33430815418348945298448389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22287210278899296865632259 33430815418348945298448389)
                ·
                  refine ⟨6268277890940427243459073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33430815418348945298448389 6268277890940427243459073)
                  ·
                    refine ⟨4701208418205320432594305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268277890940427243459073 4701208418205320432594305)
                    ·
                      refine ⟨3525906313653990324445729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701208418205320432594305 3525906313653990324445729)
                      ·
                        rfl

theorem cell23_6866678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6866678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866678 prefixEnd_6866678 := by exact prefixLift 6866678
  have htrace : WordTrace (prefixWord ++ tailWord_6866678) baseStart_6866678 baseEnd_6866678 := by
    simpa [prefixWord, tailWord_6866678, baseEnd_6866678] using wordTrace_append hprefix tailTrace_6866678
  have hstable : (prefixWord ++ tailWord_6866678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866678).length < 2 ^ (prefixWord ++ tailWord_6866678).sum := by decide
  have hdescent : baseEnd_6866678 < baseStart_6866678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866695 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6866695 : Nat := 118140960795 + 6866695 * 2 ^ 59
def prefixEnd_6866695 : Nat := 4983230072969 + 3 ^ 40 * 6866695 * 2
def baseEnd_6866695 : Nat := 3525915042825116757933151

theorem tailTrace_6866695 : CollatzResearch.WordTrace tailWord_6866695 prefixEnd_6866695 3525915042825116757933151 := by
  unfold tailWord_6866695
  simp only [CollatzResearch.WordTrace]
  refine ⟨250448941858144227984657539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166965961238762818656438359 250448941858144227984657539)
  ·
    refine ⟨375673412787216341976986309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250448941858144227984657539 375673412787216341976986309)
    ·
      refine ⟨70438764897603064120684933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375673412787216341976986309 70438764897603064120684933)
      ·
        refine ⟨13207268418300574522628425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70438764897603064120684933 13207268418300574522628425)
        ·
          refine ⟨9905451313725430891971319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13207268418300574522628425 9905451313725430891971319)
          ·
            refine ⟨14858176970588146337956979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905451313725430891971319 14858176970588146337956979)
            ·
              refine ⟨22287265455882219506935469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858176970588146337956979 22287265455882219506935469)
              ·
                refine ⟨8357724545955832315100801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22287265455882219506935469 8357724545955832315100801)
                ·
                  refine ⟨6268293409466874236325601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357724545955832315100801 6268293409466874236325601)
                  ·
                    refine ⟨4701220057100155677244201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268293409466874236325601 4701220057100155677244201)
                    ·
                      refine ⟨3525915042825116757933151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701220057100155677244201 3525915042825116757933151)
                      ·
                        rfl

theorem cell23_6866695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6866695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866695 prefixEnd_6866695 := by exact prefixLift 6866695
  have htrace : WordTrace (prefixWord ++ tailWord_6866695) baseStart_6866695 baseEnd_6866695 := by
    simpa [prefixWord, tailWord_6866695, baseEnd_6866695] using wordTrace_append hprefix tailTrace_6866695
  have hstable : (prefixWord ++ tailWord_6866695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866695).length < 2 ^ (prefixWord ++ tailWord_6866695).sum := by decide
  have hdescent : baseEnd_6866695 < baseStart_6866695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866697 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_6866697 : Nat := 118140960795 + 6866697 * 2 ^ 59
def prefixEnd_6866697 : Nat := 4983230072969 + 3 ^ 40 * 6866697 * 2
def baseEnd_6866697 : Nat := 1175305356595475250036047

theorem tailTrace_6866697 : CollatzResearch.WordTrace tailWord_6866697 prefixEnd_6866697 1175305356595475250036047 := by
  unfold tailWord_6866697
  simp only [CollatzResearch.WordTrace]
  refine ⟨250449014804136982326230345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166966009869424654884153563 250449014804136982326230345)
  ·
    refine ⟨187836761103102736744672759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250449014804136982326230345 187836761103102736744672759)
    ·
      refine ⟨281755141654654105117009139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187836761103102736744672759 281755141654654105117009139)
      ·
        refine ⟨422632712481981157675513709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281755141654654105117009139 422632712481981157675513709)
        ·
          refine ⟨158487267180742934128317641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422632712481981157675513709 158487267180742934128317641)
          ·
            refine ⟨118865450385557200596238231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158487267180742934128317641 118865450385557200596238231)
            ·
              refine ⟨178298175578335800894357347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118865450385557200596238231 178298175578335800894357347)
              ·
                refine ⟨267447263367503701341536021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178298175578335800894357347 267447263367503701341536021)
                ·
                  refine ⟨12536590470351736000384501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267447263367503701341536021 12536590470351736000384501)
                  ·
                    refine ⟨1175305356595475250036047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12536590470351736000384501 1175305356595475250036047)
                    ·
                      rfl

theorem cell23_6866697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_6866697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866697 prefixEnd_6866697 := by exact prefixLift 6866697
  have htrace : WordTrace (prefixWord ++ tailWord_6866697) baseStart_6866697 baseEnd_6866697 := by
    simpa [prefixWord, tailWord_6866697, baseEnd_6866697] using wordTrace_append hprefix tailTrace_6866697
  have hstable : (prefixWord ++ tailWord_6866697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866697).length < 2 ^ (prefixWord ++ tailWord_6866697).sum := by decide
  have hdescent : baseEnd_6866697 < baseStart_6866697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866714 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_6866714 : Nat := 118140960795 + 6866714 * 2 ^ 59
def prefixEnd_6866714 : Nat := 4983230072969 + 3 ^ 40 * 6866714 * 2
def baseEnd_6866714 : Nat := 1175308266319184061198521

theorem tailTrace_6866714 : CollatzResearch.WordTrace tailWord_6866714 prefixEnd_6866714 1175308266319184061198521 := by
  unfold tailWord_6866714
  simp only [CollatzResearch.WordTrace]
  refine ⟨62612408711268848557399799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166966423230050262819732797 62612408711268848557399799)
  ·
    refine ⟨93918613066903272836099699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62612408711268848557399799 93918613066903272836099699)
    ·
      refine ⟨140877919600354909254149549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93918613066903272836099699 140877919600354909254149549)
      ·
        refine ⟨52829219850133090970306081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140877919600354909254149549 52829219850133090970306081)
        ·
          refine ⟨39621914887599818227729561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52829219850133090970306081 39621914887599818227729561)
          ·
            refine ⟨29716436165699863670797171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39621914887599818227729561 29716436165699863670797171)
            ·
              refine ⟨44574654248549795506195757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29716436165699863670797171 44574654248549795506195757)
              ·
                refine ⟨16715495343206173314823409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44574654248549795506195757 16715495343206173314823409)
                ·
                  refine ⟨12536621507404629986117557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16715495343206173314823409 12536621507404629986117557)
                  ·
                    refine ⟨1175308266319184061198521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12536621507404629986117557 1175308266319184061198521)
                    ·
                      rfl

theorem cell23_6866714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_6866714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866714 prefixEnd_6866714 := by exact prefixLift 6866714
  have htrace : WordTrace (prefixWord ++ tailWord_6866714) baseStart_6866714 baseEnd_6866714 := by
    simpa [prefixWord, tailWord_6866714, baseEnd_6866714] using wordTrace_append hprefix tailTrace_6866714
  have hstable : (prefixWord ++ tailWord_6866714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866714).length < 2 ^ (prefixWord ++ tailWord_6866714).sum := by decide
  have hdescent : baseEnd_6866714 < baseStart_6866714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866724 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6866724 : Nat := 118140960795 + 6866724 * 2 ^ 59
def prefixEnd_6866724 : Nat := 4983230072969 + 3 ^ 40 * 6866724 * 2
def baseEnd_6866724 : Nat := 3525929933764097144470517

theorem tailTrace_6866724 : CollatzResearch.WordTrace tailWord_6866724 prefixEnd_6866724 3525929933764097144470517 := by
  unfold tailWord_6866724
  simp only [CollatzResearch.WordTrace]
  refine ⟨125224999787519582968731613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166966666383359443958308817 125224999787519582968731613)
  ·
    refine ⟨46959374920319843613274355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125224999787519582968731613 46959374920319843613274355)
    ·
      refine ⟨70439062380479765419911533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46959374920319843613274355 70439062380479765419911533)
      ·
        refine ⟨26414648392679912032466825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70439062380479765419911533 26414648392679912032466825)
        ·
          refine ⟨19810986294509934024350119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26414648392679912032466825 19810986294509934024350119)
          ·
            refine ⟨29716479441764901036525179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19810986294509934024350119 29716479441764901036525179)
            ·
              refine ⟨44574719162647351554787769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29716479441764901036525179 44574719162647351554787769)
              ·
                refine ⟨33431039371985513666090827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44574719162647351554787769 33431039371985513666090827)
                ·
                  refine ⟨50146559057978270499136241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33431039371985513666090827 50146559057978270499136241)
                  ·
                    refine ⟨37609919293483702874352181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50146559057978270499136241 37609919293483702874352181)
                    ·
                      refine ⟨3525929933764097144470517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37609919293483702874352181 3525929933764097144470517)
                      ·
                        rfl

theorem cell23_6866724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6866724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866724 prefixEnd_6866724 := by exact prefixLift 6866724
  have htrace : WordTrace (prefixWord ++ tailWord_6866724) baseStart_6866724 baseEnd_6866724 := by
    simpa [prefixWord, tailWord_6866724, baseEnd_6866724] using wordTrace_append hprefix tailTrace_6866724
  have hstable : (prefixWord ++ tailWord_6866724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866724).length < 2 ^ (prefixWord ++ tailWord_6866724).sum := by decide
  have hdescent : baseEnd_6866724 < baseStart_6866724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866778 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_6866778 : Nat := 118140960795 + 6866778 * 2 ^ 59
def prefixEnd_6866778 : Nat := 4983230072969 + 3 ^ 40 * 6866778 * 2
def baseEnd_6866778 : Nat := 1175319220573146644398423

theorem tailTrace_6866778 : CollatzResearch.WordTrace tailWord_6866778 prefixEnd_6866778 1175319220573146644398423 := by
  unfold tailWord_6866778
  simp only [CollatzResearch.WordTrace]
  refine ⟨62612992279210883289982247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166967979411229022106619325 62612992279210883289982247)
  ·
    refine ⟨93919488418816324934973371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62612992279210883289982247 93919488418816324934973371)
    ·
      refine ⟨140879232628224487402460057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93919488418816324934973371 140879232628224487402460057)
      ·
        refine ⟨105659424471168365551845043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140879232628224487402460057 105659424471168365551845043)
        ·
          refine ⟨158489136706752548327767565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105659424471168365551845043 158489136706752548327767565)
          ·
            refine ⟨59433426265032205622912837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158489136706752548327767565 59433426265032205622912837)
            ·
              refine ⟨11143767424693538554296157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59433426265032205622912837 11143767424693538554296157)
              ·
                refine ⟨4178912784260076957861059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143767424693538554296157 4178912784260076957861059)
                ·
                  refine ⟨6268369176390115436791589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178912784260076957861059 6268369176390115436791589)
                  ·
                    refine ⟨1175319220573146644398423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268369176390115436791589 1175319220573146644398423)
                    ·
                      rfl

theorem cell23_6866778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_6866778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866778 prefixEnd_6866778 := by exact prefixLift 6866778
  have htrace : WordTrace (prefixWord ++ tailWord_6866778) baseStart_6866778 baseEnd_6866778 := by
    simpa [prefixWord, tailWord_6866778, baseEnd_6866778] using wordTrace_append hprefix tailTrace_6866778
  have hstable : (prefixWord ++ tailWord_6866778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866778).length < 2 ^ (prefixWord ++ tailWord_6866778).sum := by decide
  have hdescent : baseEnd_6866778 < baseStart_6866778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866821 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_6866821 : Nat := 118140960795 + 6866821 * 2 ^ 59
def prefixEnd_6866821 : Nat := 4983230072969 + 3 ^ 40 * 6866821 * 2
def baseEnd_6866821 : Nat := 1175326580462527754985857

theorem tailTrace_6866821 : CollatzResearch.WordTrace tailWord_6866821 prefixEnd_6866821 1175326580462527754985857 := by
  unfold tailWord_6866821
  simp only [CollatzResearch.WordTrace]
  refine ⟨250453537455687751503744317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166969024970458501002496211 250453537455687751503744317)
  ·
    refine ⟨93920076545882906813904119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250453537455687751503744317 93920076545882906813904119)
    ·
      refine ⟨140880114818824360220856179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93920076545882906813904119 140880114818824360220856179)
      ·
        refine ⟨211320172228236540331284269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140880114818824360220856179 211320172228236540331284269)
        ·
          refine ⟨79245064585588702624231601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211320172228236540331284269 79245064585588702624231601)
          ·
            refine ⟨59433798439191526968173701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79245064585588702624231601 59433798439191526968173701)
            ·
              refine ⟨11143837207348411306532569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59433798439191526968173701 11143837207348411306532569)
              ·
                refine ⟨8357877905511308479899427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11143837207348411306532569 8357877905511308479899427)
                ·
                  refine ⟨12536816858266962719849141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8357877905511308479899427 12536816858266962719849141)
                  ·
                    refine ⟨1175326580462527754985857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12536816858266962719849141 1175326580462527754985857)
                    ·
                      rfl

theorem cell23_6866821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_6866821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866821 prefixEnd_6866821 := by exact prefixLift 6866821
  have htrace : WordTrace (prefixWord ++ tailWord_6866821) baseStart_6866821 baseEnd_6866821 := by
    simpa [prefixWord, tailWord_6866821, baseEnd_6866821] using wordTrace_append hprefix tailTrace_6866821
  have hstable : (prefixWord ++ tailWord_6866821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866821).length < 2 ^ (prefixWord ++ tailWord_6866821).sum := by decide
  have hdescent : baseEnd_6866821 < baseStart_6866821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866841 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_6866841 : Nat := 118140960795 + 6866841 * 2 ^ 59
def prefixEnd_6866841 : Nat := 4983230072969 + 3 ^ 40 * 6866841 * 2
def baseEnd_6866841 : Nat := 3525990011000673186707479

theorem tailTrace_6866841 : CollatzResearch.WordTrace tailWord_6866841 prefixEnd_6866841 3525990011000673186707479 := by
  unfold tailWord_6866841
  simp only [CollatzResearch.WordTrace]
  refine ⟨250454266915615294919472377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166969511277076863279648251 250454266915615294919472377)
  ·
    refine ⟨187840700186711471189604283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250454266915615294919472377 187840700186711471189604283)
    ·
      refine ⟨281761050280067206784406425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187840700186711471189604283 281761050280067206784406425)
      ·
        refine ⟨211320787710050405088304819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281761050280067206784406425 211320787710050405088304819)
        ·
          refine ⟨316981181565075607632457229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211320787710050405088304819 316981181565075607632457229)
          ·
            refine ⟨118867943086903352862171461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316981181565075607632457229 118867943086903352862171461)
            ·
              refine ⟨22287739328794378661657149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118867943086903352862171461 22287739328794378661657149)
              ·
                refine ⟨8357902248297891998121431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22287739328794378661657149 8357902248297891998121431)
                ·
                  refine ⟨12536853372446837997182147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8357902248297891998121431 12536853372446837997182147)
                  ·
                    refine ⟨18805280058670256995773221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12536853372446837997182147 18805280058670256995773221)
                    ·
                      refine ⟨3525990011000673186707479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18805280058670256995773221 3525990011000673186707479)
                      ·
                        rfl

theorem cell23_6866841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_6866841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866841 prefixEnd_6866841 := by exact prefixLift 6866841
  have htrace : WordTrace (prefixWord ++ tailWord_6866841) baseStart_6866841 baseEnd_6866841 := by
    simpa [prefixWord, tailWord_6866841, baseEnd_6866841] using wordTrace_append hprefix tailTrace_6866841
  have hstable : (prefixWord ++ tailWord_6866841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866841).length < 2 ^ (prefixWord ++ tailWord_6866841).sum := by decide
  have hdescent : baseEnd_6866841 < baseStart_6866841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866851 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 2, 4]
def baseStart_6866851 : Nat := 118140960795 + 6866851 * 2 ^ 59
def prefixEnd_6866851 : Nat := 4983230072969 + 3 ^ 40 * 6866851 * 2
def baseEnd_6866851 : Nat := 1175331715269072715860811

theorem tailTrace_6866851 : CollatzResearch.WordTrace tailWord_6866851 prefixEnd_6866851 1175331715269072715860811 := by
  unfold tailWord_6866851
  simp only [CollatzResearch.WordTrace]
  refine ⟨250454631645579066627336407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166969754430386044418224271 250454631645579066627336407)
  ·
    refine ⟨375681947468368599941004611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250454631645579066627336407 375681947468368599941004611)
    ·
      refine ⟨563522921202552899911506917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375681947468368599941004611 563522921202552899911506917)
      ·
        refine ⟨105660547725478668733407547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 563522921202552899911506917 105660547725478668733407547)
        ·
          refine ⟨158490821588218003100111321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105660547725478668733407547 158490821588218003100111321)
          ·
            refine ⟨118868116191163502325083491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158490821588218003100111321 118868116191163502325083491)
            ·
              refine ⟨178302174286745253487625237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118868116191163502325083491 178302174286745253487625237)
              ·
                refine ⟨8357914419691183757232433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178302174286745253487625237 8357914419691183757232433)
                ·
                  refine ⟨6268435814768387817924325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357914419691183757232433 6268435814768387817924325)
                  ·
                    refine ⟨1175331715269072715860811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268435814768387817924325 1175331715269072715860811)
                    ·
                      rfl

theorem cell23_6866851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 4].length) (baseStart_6866851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866851 prefixEnd_6866851 := by exact prefixLift 6866851
  have htrace : WordTrace (prefixWord ++ tailWord_6866851) baseStart_6866851 baseEnd_6866851 := by
    simpa [prefixWord, tailWord_6866851, baseEnd_6866851] using wordTrace_append hprefix tailTrace_6866851
  have hstable : (prefixWord ++ tailWord_6866851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866851).length < 2 ^ (prefixWord ++ tailWord_6866851).sum := by decide
  have hdescent : baseEnd_6866851 < baseStart_6866851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866852 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_6866852 : Nat := 118140960795 + 6866852 * 2 ^ 59
def prefixEnd_6866852 : Nat := 4983230072969 + 3 ^ 40 * 6866852 * 2
def baseEnd_6866852 : Nat := 3525995659287872643669929

theorem tailTrace_6866852 : CollatzResearch.WordTrace tailWord_6866852 prefixEnd_6866852 3525995659287872643669929 := by
  unfold tailWord_6866852
  simp only [CollatzResearch.WordTrace]
  refine ⟨125227334059287721899061405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166969778745716962532081873 125227334059287721899061405)
  ·
    refine ⟨46960250272232895712148027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125227334059287721899061405 46960250272232895712148027)
    ·
      refine ⟨70440375408349343568222041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46960250272232895712148027 70440375408349343568222041)
      ·
        refine ⟨52830281556262007676166531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70440375408349343568222041 52830281556262007676166531)
        ·
          refine ⟨79245422334393011514249797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52830281556262007676166531 79245422334393011514249797)
          ·
            refine ⟨14858516687698689658921837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79245422334393011514249797 14858516687698689658921837)
            ·
              refine ⟨5571943757887008622095689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14858516687698689658921837 5571943757887008622095689)
              ·
                refine ⟨4178957818415256466571767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571943757887008622095689 4178957818415256466571767)
                ·
                  refine ⟨6268436727622884699857651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178957818415256466571767 6268436727622884699857651)
                  ·
                    refine ⟨9402655091434327049786477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6268436727622884699857651 9402655091434327049786477)
                    ·
                      refine ⟨3525995659287872643669929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402655091434327049786477 3525995659287872643669929)
                      ·
                        rfl

theorem cell23_6866852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_6866852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866852 prefixEnd_6866852 := by exact prefixLift 6866852
  have htrace : WordTrace (prefixWord ++ tailWord_6866852) baseStart_6866852 baseEnd_6866852 := by
    simpa [prefixWord, tailWord_6866852, baseEnd_6866852] using wordTrace_append hprefix tailTrace_6866852
  have hstable : (prefixWord ++ tailWord_6866852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866852).length < 2 ^ (prefixWord ++ tailWord_6866852).sum := by decide
  have hdescent : baseEnd_6866852 < baseStart_6866852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866878 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_6866878 : Nat := 118140960795 + 6866878 * 2 ^ 59
def prefixEnd_6866878 : Nat := 4983230072969 + 3 ^ 40 * 6866878 * 2
def baseEnd_6866878 : Nat := 3526009009784889541944809

theorem tailTrace_6866878 : CollatzResearch.WordTrace tailWord_6866878 prefixEnd_6866878 3526009009784889541944809 := by
  unfold tailWord_6866878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31306952052060156279821161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166970410944320833492379525 31306952052060156279821161)
  ·
    refine ⟨23480214039045117209865871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31306952052060156279821161 23480214039045117209865871)
    ·
      refine ⟨35220321058567675814798807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23480214039045117209865871 35220321058567675814798807)
      ·
        refine ⟨52830481587851513722198211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35220321058567675814798807 52830481587851513722198211)
        ·
          refine ⟨79245722381777270583297317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52830481587851513722198211 79245722381777270583297317)
          ·
            refine ⟨14858572946583238234368247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79245722381777270583297317 14858572946583238234368247)
            ·
              refine ⟨22287859419874857351552371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858572946583238234368247 22287859419874857351552371)
              ·
                refine ⟨33431789129812286027328557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22287859419874857351552371 33431789129812286027328557)
                ·
                  refine ⟨12536920923679607260248209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33431789129812286027328557 12536920923679607260248209)
                  ·
                    refine ⟨9402690692759705445186157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12536920923679607260248209 9402690692759705445186157)
                    ·
                      refine ⟨3526009009784889541944809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402690692759705445186157 3526009009784889541944809)
                      ·
                        rfl

theorem cell23_6866878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_6866878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866878 prefixEnd_6866878 := by exact prefixLift 6866878
  have htrace : WordTrace (prefixWord ++ tailWord_6866878) baseStart_6866878 baseEnd_6866878 := by
    simpa [prefixWord, tailWord_6866878, baseEnd_6866878] using wordTrace_append hprefix tailTrace_6866878
  have hstable : (prefixWord ++ tailWord_6866878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866878).length < 2 ^ (prefixWord ++ tailWord_6866878).sum := by decide
  have hdescent : baseEnd_6866878 < baseStart_6866878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866891 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3]
def baseStart_6866891 : Nat := 118140960795 + 6866891 * 2 ^ 59
def prefixEnd_6866891 : Nat := 4983230072969 + 3 ^ 40 * 6866891 * 2
def baseEnd_6866891 : Nat := 3526015685033397991082249

theorem tailTrace_6866891 : CollatzResearch.WordTrace tailWord_6866891 prefixEnd_6866891 3526015685033397991082249 := by
  unfold tailWord_6866891
  simp only [CollatzResearch.WordTrace]
  refine ⟨250456090565434153458792527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166970727043622768972528351 250456090565434153458792527)
  ·
    refine ⟨375684135848151230188188791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250456090565434153458792527 375684135848151230188188791)
    ·
      refine ⟨563526203772226845282283187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375684135848151230188188791 563526203772226845282283187)
      ·
        refine ⟨845289305658340267923424781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563526203772226845282283187 845289305658340267923424781)
        ·
          refine ⟨316983489621877600471284293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 845289305658340267923424781 316983489621877600471284293)
          ·
            refine ⟨59434404304102050088365805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316983489621877600471284293 59434404304102050088365805)
            ·
              refine ⟨22287901614038268783137177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59434404304102050088365805 22287901614038268783137177)
              ·
                refine ⟨16715926210528701587352883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22287901614038268783137177 16715926210528701587352883)
                ·
                  refine ⟨25073889315793052381029325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16715926210528701587352883 25073889315793052381029325)
                  ·
                    refine ⟨9402708493422394642885997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25073889315793052381029325 9402708493422394642885997)
                    ·
                      refine ⟨3526015685033397991082249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9402708493422394642885997 3526015685033397991082249)
                      ·
                        rfl

theorem cell23_6866891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3].length) (baseStart_6866891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866891 prefixEnd_6866891 := by exact prefixLift 6866891
  have htrace : WordTrace (prefixWord ++ tailWord_6866891) baseStart_6866891 baseEnd_6866891 := by
    simpa [prefixWord, tailWord_6866891, baseEnd_6866891] using wordTrace_append hprefix tailTrace_6866891
  have hstable : (prefixWord ++ tailWord_6866891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866891).length < 2 ^ (prefixWord ++ tailWord_6866891).sum := by decide
  have hdescent : baseEnd_6866891 < baseStart_6866891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866902 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6866902 : Nat := 118140960795 + 6866902 * 2 ^ 59
def prefixEnd_6866902 : Nat := 4983230072969 + 3 ^ 40 * 6866902 * 2
def baseEnd_6866902 : Nat := 1175340444440199149348233

theorem tailTrace_6866902 : CollatzResearch.WordTrace tailWord_6866902 prefixEnd_6866902 1175340444440199149348233 := by
  unfold tailWord_6866902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653530735524643896090185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166970994512262868224961973 15653530735524643896090185)
  ·
    refine ⟨11740148051643482922067639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15653530735524643896090185 11740148051643482922067639)
    ·
      refine ⟨17610222077465224383101459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11740148051643482922067639 17610222077465224383101459)
      ·
        refine ⟨26415333116197836574652189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17610222077465224383101459 26415333116197836574652189)
        ·
          refine ⟨9905749918574188715494571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26415333116197836574652189 9905749918574188715494571)
          ·
            refine ⟨14858624877861283073241857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905749918574188715494571 14858624877861283073241857)
            ·
              refine ⟨11143968658395962304931393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14858624877861283073241857 11143968658395962304931393)
              ·
                refine ⟨8357976493796971728698545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11143968658395962304931393 8357976493796971728698545)
                ·
                  refine ⟨6268482370347728796523909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357976493796971728698545 6268482370347728796523909)
                  ·
                    refine ⟨1175340444440199149348233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268482370347728796523909 1175340444440199149348233)
                    ·
                      rfl

theorem cell23_6866902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6866902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866902 prefixEnd_6866902 := by exact prefixLift 6866902
  have htrace : WordTrace (prefixWord ++ tailWord_6866902) baseStart_6866902 baseEnd_6866902 := by
    simpa [prefixWord, tailWord_6866902, baseEnd_6866902] using wordTrace_append hprefix tailTrace_6866902
  have hstable : (prefixWord ++ tailWord_6866902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866902).length < 2 ^ (prefixWord ++ tailWord_6866902).sum := by decide
  have hdescent : baseEnd_6866902 < baseStart_6866902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6866909 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6866909 : Nat := 118140960795 + 6866909 * 2 ^ 59
def prefixEnd_6866909 : Nat := 4983230072969 + 3 ^ 40 * 6866909 * 2
def baseEnd_6866909 : Nat := 3526024927685178920657167

theorem tailTrace_6866909 : CollatzResearch.WordTrace tailWord_6866909 prefixEnd_6866909 3526024927685178920657167 := by
  unfold tailWord_6866909
  simp only [CollatzResearch.WordTrace]
  refine ⟨250456747079368942532947781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166971164719579295021965187 250456747079368942532947781)
  ·
    refine ⟨46960640077381676724927709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250456747079368942532947781 46960640077381676724927709)
    ·
      refine ⟨17610240029018128771847891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46960640077381676724927709 17610240029018128771847891)
      ·
        refine ⟨26415360043527193157771837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17610240029018128771847891 26415360043527193157771837)
        ·
          refine ⟨9905760016322697434164439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26415360043527193157771837 9905760016322697434164439)
          ·
            refine ⟨14858640024484046151246659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905760016322697434164439 14858640024484046151246659)
            ·
              refine ⟨22287960036726069226869989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858640024484046151246659 22287960036726069226869989)
              ·
                refine ⟨4178992506886137980038123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22287960036726069226869989 4178992506886137980038123)
                ·
                  refine ⟨6268488760329206970057185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178992506886137980038123 6268488760329206970057185)
                  ·
                    refine ⟨4701366570246905227542889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268488760329206970057185 4701366570246905227542889)
                    ·
                      refine ⟨3526024927685178920657167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701366570246905227542889 3526024927685178920657167)
                      ·
                        rfl

theorem cell23_6866909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6866909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6866909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6866909 prefixEnd_6866909 := by exact prefixLift 6866909
  have htrace : WordTrace (prefixWord ++ tailWord_6866909) baseStart_6866909 baseEnd_6866909 := by
    simpa [prefixWord, tailWord_6866909, baseEnd_6866909] using wordTrace_append hprefix tailTrace_6866909
  have hstable : (prefixWord ++ tailWord_6866909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6866909).length < 2 ^ (prefixWord ++ tailWord_6866909).sum := by decide
  have hdescent : baseEnd_6866909 < baseStart_6866909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6866909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867081 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_6867081 : Nat := 118140960795 + 6867081 * 2 ^ 59
def prefixEnd_6867081 : Nat := 4983230072969 + 3 ^ 40 * 6867081 * 2
def baseEnd_6867081 : Nat := 3526113246357752247706375

theorem tailTrace_6867081 : CollatzResearch.WordTrace tailWord_6867081 prefixEnd_6867081 3526113246357752247706375 := by
  unfold tailWord_6867081
  simp only [CollatzResearch.WordTrace]
  refine ⟨250463020434745815908209097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166975346956497210605472731 250463020434745815908209097)
  ·
    refine ⟨187847265326059361931156823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250463020434745815908209097 187847265326059361931156823)
    ·
      refine ⟨281770897989089042896735235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187847265326059361931156823 281770897989089042896735235)
      ·
        refine ⟨422656346983633564345102853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281770897989089042896735235 422656346983633564345102853)
        ·
          refine ⟨79248065059431293314706785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422656346983633564345102853 79248065059431293314706785)
          ·
            refine ⟨59436048794573469986030089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79248065059431293314706785 59436048794573469986030089)
            ·
              refine ⟨44577036595930102489522567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59436048794573469986030089 44577036595930102489522567)
              ·
                refine ⟨66865554893895153734283851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44577036595930102489522567 66865554893895153734283851)
                ·
                  refine ⟨100298332340842730601425777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66865554893895153734283851 100298332340842730601425777)
                  ·
                    refine ⟨75223749255632047951069333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100298332340842730601425777 75223749255632047951069333)
                    ·
                      refine ⟨3526113246357752247706375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75223749255632047951069333 3526113246357752247706375)
                      ·
                        rfl

theorem cell23_6867081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_6867081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867081 prefixEnd_6867081 := by exact prefixLift 6867081
  have htrace : WordTrace (prefixWord ++ tailWord_6867081) baseStart_6867081 baseEnd_6867081 := by
    simpa [prefixWord, tailWord_6867081, baseEnd_6867081] using wordTrace_append hprefix tailTrace_6867081
  have hstable : (prefixWord ++ tailWord_6867081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867081).length < 2 ^ (prefixWord ++ tailWord_6867081).sum := by decide
  have hdescent : baseEnd_6867081 < baseStart_6867081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867082 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_6867082 : Nat := 118140960795 + 6867082 * 2 ^ 59
def prefixEnd_6867082 : Nat := 4983230072969 + 3 ^ 40 * 6867082 * 2
def baseEnd_6867082 : Nat := 1175371253279468914597957

theorem tailTrace_6867082 : CollatzResearch.WordTrace tailWord_6867082 prefixEnd_6867082 1175371253279468914597957 := by
  unfold tailWord_6867082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62615764226935548269748875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166975371271828128719330333 62615764226935548269748875)
  ·
    refine ⟨93923646340403322404623313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62615764226935548269748875 93923646340403322404623313)
    ·
      refine ⟨70442734755302491803467485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93923646340403322404623313 70442734755302491803467485)
      ·
        refine ⟨26416025533238434426300307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70442734755302491803467485 26416025533238434426300307)
        ·
          refine ⟨39624038299857651639450461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26416025533238434426300307 39624038299857651639450461)
          ·
            refine ⟨14859014362446619364793923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39624038299857651639450461 14859014362446619364793923)
            ·
              refine ⟨22288521543669929047190885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14859014362446619364793923 22288521543669929047190885)
              ·
                refine ⟨4179097789438111696348291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22288521543669929047190885 4179097789438111696348291)
                ·
                  refine ⟨6268646684157167544522437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179097789438111696348291 6268646684157167544522437)
                  ·
                    refine ⟨1175371253279468914597957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268646684157167544522437 1175371253279468914597957)
                    ·
                      rfl

theorem cell23_6867082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_6867082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867082 prefixEnd_6867082 := by exact prefixLift 6867082
  have htrace : WordTrace (prefixWord ++ tailWord_6867082) baseStart_6867082 baseEnd_6867082 := by
    simpa [prefixWord, tailWord_6867082, baseEnd_6867082] using wordTrace_append hprefix tailTrace_6867082
  have hstable : (prefixWord ++ tailWord_6867082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867082).length < 2 ^ (prefixWord ++ tailWord_6867082).sum := by decide
  have hdescent : baseEnd_6867082 < baseStart_6867082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867105 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6867105 : Nat := 118140960795 + 6867105 * 2 ^ 59
def prefixEnd_6867105 : Nat := 4983230072969 + 3 ^ 40 * 6867105 * 2
def baseEnd_6867105 : Nat := 3526125569893460153806265

theorem tailTrace_6867105 : CollatzResearch.WordTrace tailWord_6867105 prefixEnd_6867105 3526125569893460153806265 := by
  unfold tailWord_6867105
  simp only [CollatzResearch.WordTrace]
  refine ⟨250463895786658868007082769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166975930524439245338055179 250463895786658868007082769)
  ·
    refine ⟨187847921839994151005312077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250463895786658868007082769 187847921839994151005312077)
    ·
      refine ⟨70442970689997806626992029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187847921839994151005312077 70442970689997806626992029)
      ·
        refine ⟨26416114008749177485122011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70442970689997806626992029 26416114008749177485122011)
        ·
          refine ⟨39624171013123766227683017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26416114008749177485122011 39624171013123766227683017)
          ·
            refine ⟨29718128259842824670762263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39624171013123766227683017 29718128259842824670762263)
            ·
              refine ⟨44577192389764237006143395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29718128259842824670762263 44577192389764237006143395)
              ·
                refine ⟨66865788584646355509215093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44577192389764237006143395 66865788584646355509215093)
                ·
                  refine ⟨6268667679810595828988915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66865788584646355509215093 6268667679810595828988915)
                  ·
                    refine ⟨9403001519715893743483373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6268667679810595828988915 9403001519715893743483373)
                    ·
                      refine ⟨3526125569893460153806265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9403001519715893743483373 3526125569893460153806265)
                      ·
                        rfl

theorem cell23_6867105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6867105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867105 prefixEnd_6867105 := by exact prefixLift 6867105
  have htrace : WordTrace (prefixWord ++ tailWord_6867105) baseStart_6867105 baseEnd_6867105 := by
    simpa [prefixWord, tailWord_6867105, baseEnd_6867105] using wordTrace_append hprefix tailTrace_6867105
  have hstable : (prefixWord ++ tailWord_6867105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867105).length < 2 ^ (prefixWord ++ tailWord_6867105).sum := by decide
  have hdescent : baseEnd_6867105 < baseStart_6867105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867151 : List Nat := [1, 1, 2, 1, 1, 3, 4, 10]
def baseStart_6867151 : Nat := 118140960795 + 6867151 * 2 ^ 59
def prefixEnd_6867151 : Nat := 4983230072969 + 3 ^ 40 * 6867151 * 2
def baseEnd_6867151 : Nat := 130598118148280258290039

theorem tailTrace_6867151 : CollatzResearch.WordTrace tailWord_6867151 prefixEnd_6867151 130598118148280258290039 := by
  unfold tailWord_6867151
  simp only [CollatzResearch.WordTrace]
  refine ⟨250465573544492217863257307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166977049029661478575504871 250465573544492217863257307)
  ·
    refine ⟨375698360316738326794885961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250465573544492217863257307 375698360316738326794885961)
    ·
      refine ⟨281773770237553745096164471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375698360316738326794885961 281773770237553745096164471)
      ·
        refine ⟨422660655356330617644246707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281773770237553745096164471 422660655356330617644246707)
        ·
          refine ⟨633990983034495926466370061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422660655356330617644246707 633990983034495926466370061)
          ·
            refine ⟨237746618637935972424888773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633990983034495926466370061 237746618637935972424888773)
            ·
              refine ⟨44577490994612994829666645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237746618637935972424888773 44577490994612994829666645)
              ·
                refine ⟨130598118148280258290039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44577490994612994829666645 130598118148280258290039)
                ·
                  rfl

theorem cell23_6867151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 10].length) (baseStart_6867151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867151 prefixEnd_6867151 := by exact prefixLift 6867151
  have htrace : WordTrace (prefixWord ++ tailWord_6867151) baseStart_6867151 baseEnd_6867151 := by
    simpa [prefixWord, tailWord_6867151, baseEnd_6867151] using wordTrace_append hprefix tailTrace_6867151
  have hstable : (prefixWord ++ tailWord_6867151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867151).length < 2 ^ (prefixWord ++ tailWord_6867151).sum := by decide
  have hdescent : baseEnd_6867151 < baseStart_6867151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867162 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_6867162 : Nat := 118140960795 + 6867162 * 2 ^ 59
def prefixEnd_6867162 : Nat := 4983230072969 + 3 ^ 40 * 6867162 * 2
def baseEnd_6867162 : Nat := 3526154838290766430793503

theorem tailTrace_6867162 : CollatzResearch.WordTrace tailWord_6867162 prefixEnd_6867162 3526154838290766430793503 := by
  unfold tailWord_6867162
  simp only [CollatzResearch.WordTrace]
  refine ⟨62616493686863091685476935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166977316498301577827938493 62616493686863091685476935)
  ·
    refine ⟨93924740530294637528215403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62616493686863091685476935 93924740530294637528215403)
    ·
      refine ⟨140887110795441956292323105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93924740530294637528215403 140887110795441956292323105)
      ·
        refine ⟨105665333096581467219242329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140887110795441956292323105 105665333096581467219242329)
        ·
          refine ⟨79248999822436100414431747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105665333096581467219242329 79248999822436100414431747)
          ·
            refine ⟨118873499733654150621647621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79248999822436100414431747 118873499733654150621647621)
            ·
              refine ⟨22288781200060153241558929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118873499733654150621647621 22288781200060153241558929)
              ·
                refine ⟨16716585900045114931169197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22288781200060153241558929 16716585900045114931169197)
                ·
                  refine ⟨6268719712516918099188449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16716585900045114931169197 6268719712516918099188449)
                  ·
                    refine ⟨4701539784387688574391337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268719712516918099188449 4701539784387688574391337)
                    ·
                      refine ⟨3526154838290766430793503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701539784387688574391337 3526154838290766430793503)
                      ·
                        rfl

theorem cell23_6867162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_6867162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867162 prefixEnd_6867162 := by exact prefixLift 6867162
  have htrace : WordTrace (prefixWord ++ tailWord_6867162) baseStart_6867162 baseEnd_6867162 := by
    simpa [prefixWord, tailWord_6867162, baseEnd_6867162] using wordTrace_append hprefix tailTrace_6867162
  have hstable : (prefixWord ++ tailWord_6867162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867162).length < 2 ^ (prefixWord ++ tailWord_6867162).sum := by decide
  have hdescent : baseEnd_6867162 < baseStart_6867162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867212 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_6867212 : Nat := 118140960795 + 6867212 * 2 ^ 59
def prefixEnd_6867212 : Nat := 4983230072969 + 3 ^ 40 * 6867212 * 2
def baseEnd_6867212 : Nat := 3526180512323491235168273

theorem tailTrace_6867212 : CollatzResearch.WordTrace tailWord_6867212 prefixEnd_6867212 3526180512323491235168273 := by
  unfold tailWord_6867212
  simp only [CollatzResearch.WordTrace]
  refine ⟨125233899198635612640613945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166978532264847483520818593 125233899198635612640613945)
  ·
    refine ⟨93925424398976709480460459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125233899198635612640613945 93925424398976709480460459)
    ·
      refine ⟨140888136598465064220690689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93925424398976709480460459 140888136598465064220690689)
      ·
        refine ⟨105666102448848798165518017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140888136598465064220690689 105666102448848798165518017)
        ·
          refine ⟨79249576836636598624138513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105666102448848798165518017 79249576836636598624138513)
          ·
            refine ⟨59437182627477448968103885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79249576836636598624138513 59437182627477448968103885)
            ·
              refine ⟨22288943485304043363038957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59437182627477448968103885 22288943485304043363038957)
              ·
                refine ⟨8358353806989016261139609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22288943485304043363038957 8358353806989016261139609)
                ·
                  refine ⟨6268765355241762195854707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8358353806989016261139609 6268765355241762195854707)
                  ·
                    refine ⟨9403148032862643293782061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6268765355241762195854707 9403148032862643293782061)
                    ·
                      refine ⟨3526180512323491235168273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9403148032862643293782061 3526180512323491235168273)
                      ·
                        rfl

theorem cell23_6867212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_6867212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867212 prefixEnd_6867212 := by exact prefixLift 6867212
  have htrace : WordTrace (prefixWord ++ tailWord_6867212) baseStart_6867212 baseEnd_6867212 := by
    simpa [prefixWord, tailWord_6867212, baseEnd_6867212] using wordTrace_append hprefix tailTrace_6867212
  have hstable : (prefixWord ++ tailWord_6867212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867212).length < 2 ^ (prefixWord ++ tailWord_6867212).sum := by decide
  have hdescent : baseEnd_6867212 < baseStart_6867212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867228 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6867228 : Nat := 118140960795 + 6867228 * 2 ^ 59
def prefixEnd_6867228 : Nat := 4983230072969 + 3 ^ 40 * 6867228 * 2
def baseEnd_6867228 : Nat := 1175396242671321057522733

theorem tailTrace_6867228 : CollatzResearch.WordTrace tailWord_6867228 prefixEnd_6867228 1175396242671321057522733 := by
  unfold tailWord_6867228
  simp only [CollatzResearch.WordTrace]
  refine ⟨125234190982606630006905169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166978921310142173342540225 125234190982606630006905169)
  ·
    refine ⟨93925643236954972505178877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125234190982606630006905169 93925643236954972505178877)
    ·
      refine ⟨35222116213858114689442079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93925643236954972505178877 35222116213858114689442079)
      ·
        refine ⟨52833174320787172034163119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35222116213858114689442079 52833174320787172034163119)
        ·
          refine ⟨79249761481180758051244679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52833174320787172034163119 79249761481180758051244679)
          ·
            refine ⟨118874642221771137076867019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79249761481180758051244679 118874642221771137076867019)
            ·
              refine ⟨178311963332656705615300529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118874642221771137076867019 178311963332656705615300529)
              ·
                refine ⟨133733972499492529211475397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178311963332656705615300529 133733972499492529211475397)
                ·
                  refine ⟨25075119843654849227151637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133733972499492529211475397 25075119843654849227151637)
                  ·
                    refine ⟨1175396242671321057522733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25075119843654849227151637 1175396242671321057522733)
                    ·
                      rfl

theorem cell23_6867228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6867228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867228 prefixEnd_6867228 := by exact prefixLift 6867228
  have htrace : WordTrace (prefixWord ++ tailWord_6867228) baseStart_6867228 baseEnd_6867228 := by
    simpa [prefixWord, tailWord_6867228, baseEnd_6867228] using wordTrace_append hprefix tailTrace_6867228
  have hstable : (prefixWord ++ tailWord_6867228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867228).length < 2 ^ (prefixWord ++ tailWord_6867228).sum := by decide
  have hdescent : baseEnd_6867228 < baseStart_6867228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867325 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_6867325 : Nat := 118140960795 + 6867325 * 2 ^ 59
def prefixEnd_6867325 : Nat := 4983230072969 + 3 ^ 40 * 6867325 * 2
def baseEnd_6867325 : Nat := 3526238535637449293055253

theorem tailTrace_6867325 : CollatzResearch.WordTrace tailWord_6867325 prefixEnd_6867325 3526238535637449293055253 := by
  unfold tailWord_6867325
  simp only [CollatzResearch.WordTrace]
  refine ⟨250471919845861845580091429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166981279897241230386727619 250471919845861845580091429)
  ·
    refine ⟨46963484971099096046267143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250471919845861845580091429 46963484971099096046267143)
    ·
      refine ⟨70445227456648644069400715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46963484971099096046267143 70445227456648644069400715)
      ·
        refine ⟨105667841184972966104101073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70445227456648644069400715 105667841184972966104101073)
        ·
          refine ⟨79250880888729724578075805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105667841184972966104101073 79250880888729724578075805)
          ·
            refine ⟨29719080333273646716778427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79250880888729724578075805 29719080333273646716778427)
            ·
              refine ⟨44578620499910470075167641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29719080333273646716778427 44578620499910470075167641)
              ·
                refine ⟨33433965374932852556375731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44578620499910470075167641 33433965374932852556375731)
                ·
                  refine ⟨50150948062399278834563597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33433965374932852556375731 50150948062399278834563597)
                  ·
                    refine ⟨18806605523399729562961349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50150948062399278834563597 18806605523399729562961349)
                    ·
                      refine ⟨3526238535637449293055253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18806605523399729562961349 3526238535637449293055253)
                      ·
                        rfl

theorem cell23_6867325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_6867325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867325 prefixEnd_6867325 := by exact prefixLift 6867325
  have htrace : WordTrace (prefixWord ++ tailWord_6867325) baseStart_6867325 baseEnd_6867325 := by
    simpa [prefixWord, tailWord_6867325, baseEnd_6867325] using wordTrace_append hprefix tailTrace_6867325
  have hstable : (prefixWord ++ tailWord_6867325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867325).length < 2 ^ (prefixWord ++ tailWord_6867325).sum := by decide
  have hdescent : baseEnd_6867325 < baseStart_6867325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867342 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6867342 : Nat := 118140960795 + 6867342 * 2 ^ 59
def prefixEnd_6867342 : Nat := 4983230072969 + 3 ^ 40 * 6867342 * 2
def baseEnd_6867342 : Nat := 3526247264808575726542675

theorem tailTrace_6867342 : CollatzResearch.WordTrace tailWord_6867342 prefixEnd_6867342 3526247264808575726542675 := by
  unfold tailWord_6867342
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309067485850032185432535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166981693257866838322306853 31309067485850032185432535)
  ·
    refine ⟨46963601228775048278148803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31309067485850032185432535 46963601228775048278148803)
    ·
      refine ⟨70445401843162572417223205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46963601228775048278148803 70445401843162572417223205)
      ·
        refine ⟨13208512845592982328229351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70445401843162572417223205 13208512845592982328229351)
        ·
          refine ⟨19812769268389473492344027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13208512845592982328229351 19812769268389473492344027)
          ·
            refine ⟨29719153902584210238516041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19812769268389473492344027 29719153902584210238516041)
            ·
              refine ⟨22289365426938157678887031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29719153902584210238516041 22289365426938157678887031)
              ·
                refine ⟨33434048140407236518330547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22289365426938157678887031 33434048140407236518330547)
                ·
                  refine ⟨50151072210610854777495821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33434048140407236518330547 50151072210610854777495821)
                  ·
                    refine ⟨18806652078979070541560933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50151072210610854777495821 18806652078979070541560933)
                    ·
                      refine ⟨3526247264808575726542675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18806652078979070541560933 3526247264808575726542675)
                      ·
                        rfl

theorem cell23_6867342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6867342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867342 prefixEnd_6867342 := by exact prefixLift 6867342
  have htrace : WordTrace (prefixWord ++ tailWord_6867342) baseStart_6867342 baseEnd_6867342 := by
    simpa [prefixWord, tailWord_6867342, baseEnd_6867342] using wordTrace_append hprefix tailTrace_6867342
  have hstable : (prefixWord ++ tailWord_6867342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867342).length < 2 ^ (prefixWord ++ tailWord_6867342).sum := by decide
  have hdescent : baseEnd_6867342 < baseStart_6867342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867365 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 6]
def baseStart_6867365 : Nat := 118140960795 + 6867365 * 2 ^ 59
def prefixEnd_6867365 : Nat := 4983230072969 + 3 ^ 40 * 6867365 * 2
def baseEnd_6867365 : Nat := 391806563873736570728341

theorem tailTrace_6867365 : CollatzResearch.WordTrace tailWord_6867365 prefixEnd_6867365 391806563873736570728341 := by
  unfold tailWord_6867365
  simp only [CollatzResearch.WordTrace]
  refine ⟨250473378765716932411547549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166982252510477954941031699 250473378765716932411547549)
  ·
    refine ⟨93927517037143849654330331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250473378765716932411547549 93927517037143849654330331)
    ·
      refine ⟨140891275555715774481495497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93927517037143849654330331 140891275555715774481495497)
      ·
        refine ⟨105668456666786830861121623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140891275555715774481495497 105668456666786830861121623)
        ·
          refine ⟨158502685000180246291682435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105668456666786830861121623 158502685000180246291682435)
          ·
            refine ⟨237754027500270369437523653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158502685000180246291682435 237754027500270369437523653)
            ·
              refine ⟨44578880156300694269535685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237754027500270369437523653 44578880156300694269535685)
              ·
                refine ⟨8358540029306380175537941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44578880156300694269535685 8358540029306380175537941)
                ·
                  refine ⟨391806563873736570728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8358540029306380175537941 391806563873736570728341)
                  ·
                    rfl

theorem cell23_6867365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_6867365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867365 prefixEnd_6867365 := by exact prefixLift 6867365
  have htrace : WordTrace (prefixWord ++ tailWord_6867365) baseStart_6867365 baseEnd_6867365 := by
    simpa [prefixWord, tailWord_6867365, baseEnd_6867365] using wordTrace_append hprefix tailTrace_6867365
  have hstable : (prefixWord ++ tailWord_6867365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867365).length < 2 ^ (prefixWord ++ tailWord_6867365).sum := by decide
  have hdescent : baseEnd_6867365 < baseStart_6867365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867392 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3]
def baseStart_6867392 : Nat := 118140960795 + 6867392 * 2 ^ 59
def prefixEnd_6867392 : Nat := 4983230072969 + 3 ^ 40 * 6867392 * 2
def baseEnd_6867392 : Nat := 3526272938841300530917445

theorem tailTrace_6867392 : CollatzResearch.WordTrace tailWord_6867392 prefixEnd_6867392 3526272938841300530917445 := by
  unfold tailWord_6867392
  simp only [CollatzResearch.WordTrace]
  refine ⟨125237181768309558011390215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166982909024412744015186953 125237181768309558011390215)
  ·
    refine ⟨187855772652464337017085323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125237181768309558011390215 187855772652464337017085323)
    ·
      refine ⟨281783658978696505525627985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187855772652464337017085323 281783658978696505525627985)
      ·
        refine ⟨211337744234022379144220989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281783658978696505525627985 211337744234022379144220989)
        ·
          refine ⟨79251654087758392179082871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211337744234022379144220989 79251654087758392179082871)
          ·
            refine ⟨118877481131637588268624307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79251654087758392179082871 118877481131637588268624307)
            ·
              refine ⟨178316221697456382402936461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118877481131637588268624307 178316221697456382402936461)
              ·
                refine ⟨66868583136546143401101173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178316221697456382402936461 66868583136546143401101173)
                ·
                  refine ⟨6268929669051200943853235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66868583136546143401101173 6268929669051200943853235)
                  ·
                    refine ⟨9403394503576801415779853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6268929669051200943853235 9403394503576801415779853)
                    ·
                      refine ⟨3526272938841300530917445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9403394503576801415779853 3526272938841300530917445)
                      ·
                        rfl

theorem cell23_6867392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_6867392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867392 prefixEnd_6867392 := by exact prefixLift 6867392
  have htrace : WordTrace (prefixWord ++ tailWord_6867392) baseStart_6867392 baseEnd_6867392 := by
    simpa [prefixWord, tailWord_6867392, baseEnd_6867392] using wordTrace_append hprefix tailTrace_6867392
  have hstable : (prefixWord ++ tailWord_6867392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867392).length < 2 ^ (prefixWord ++ tailWord_6867392).sum := by decide
  have hdescent : baseEnd_6867392 < baseStart_6867392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867393 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6867393 : Nat := 118140960795 + 6867393 * 2 ^ 59
def prefixEnd_6867393 : Nat := 4983230072969 + 3 ^ 40 * 6867393 * 2
def baseEnd_6867393 : Nat := 3526273452321955027004941

theorem tailTrace_6867393 : CollatzResearch.WordTrace tailWord_6867393 prefixEnd_6867393 3526273452321955027004941 := by
  unfold tailWord_6867393
  simp only [CollatzResearch.WordTrace]
  refine ⟨250474400009615493193566833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166982933339743662129044555 250474400009615493193566833)
  ·
    refine ⟨187855800007211619895175125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250474400009615493193566833 187855800007211619895175125)
    ·
      refine ⟨4402870312669022341293167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 187855800007211619895175125 4402870312669022341293167)
      ·
        refine ⟨6604305469003533511939751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402870312669022341293167 6604305469003533511939751)
        ·
          refine ⟨9906458203505300267909627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604305469003533511939751 9906458203505300267909627)
          ·
            refine ⟨14859687305257950401864441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9906458203505300267909627 14859687305257950401864441)
            ·
              refine ⟨11144765478943462801398331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14859687305257950401864441 11144765478943462801398331)
              ·
                refine ⟨16717148218415194202097497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144765478943462801398331 16717148218415194202097497)
                ·
                  refine ⟨12537861163811395651573123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16717148218415194202097497 12537861163811395651573123)
                  ·
                    refine ⟨18806791745717093477359685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12537861163811395651573123 18806791745717093477359685)
                    ·
                      refine ⟨3526273452321955027004941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18806791745717093477359685 3526273452321955027004941)
                      ·
                        rfl

theorem cell23_6867393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6867393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867393 prefixEnd_6867393 := by exact prefixLift 6867393
  have htrace : WordTrace (prefixWord ++ tailWord_6867393) baseStart_6867393 baseEnd_6867393 := by
    simpa [prefixWord, tailWord_6867393, baseEnd_6867393] using wordTrace_append hprefix tailTrace_6867393
  have hstable : (prefixWord ++ tailWord_6867393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867393).length < 2 ^ (prefixWord ++ tailWord_6867393).sum := by decide
  have hdescent : baseEnd_6867393 < baseStart_6867393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867396 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6867396 : Nat := 118140960795 + 6867396 * 2 ^ 59
def prefixEnd_6867396 : Nat := 4983230072969 + 3 ^ 40 * 6867396 * 2
def baseEnd_6867396 : Nat := 3526274992763918515267427

theorem tailTrace_6867396 : CollatzResearch.WordTrace tailWord_6867396 prefixEnd_6867396 3526274992763918515267427 := by
  unfold tailWord_6867396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125237254714302312352963021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166983006285736416470617361 125237254714302312352963021)
  ·
    refine ⟨46963970517863367132361133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125237254714302312352963021 46963970517863367132361133)
    ·
      refine ⟨17611488944198762674635425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46963970517863367132361133 17611488944198762674635425)
      ·
        refine ⟨13208616708149072005976569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17611488944198762674635425 13208616708149072005976569)
        ·
          refine ⟨9906462531111804004482427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13208616708149072005976569 9906462531111804004482427)
          ·
            refine ⟨14859693796667706006723641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9906462531111804004482427 14859693796667706006723641)
            ·
              refine ⟨11144770347500779505042731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14859693796667706006723641 11144770347500779505042731)
              ·
                refine ⟨16717155521251169257564097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144770347500779505042731 16717155521251169257564097)
                ·
                  refine ⟨12537866640938376943173073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16717155521251169257564097 12537866640938376943173073)
                  ·
                    refine ⟨9403399980703782707379805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12537866640938376943173073 9403399980703782707379805)
                    ·
                      refine ⟨3526274992763918515267427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9403399980703782707379805 3526274992763918515267427)
                      ·
                        rfl

theorem cell23_6867396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6867396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867396 prefixEnd_6867396 := by exact prefixLift 6867396
  have htrace : WordTrace (prefixWord ++ tailWord_6867396) baseStart_6867396 baseEnd_6867396 := by
    simpa [prefixWord, tailWord_6867396, baseEnd_6867396] using wordTrace_append hprefix tailTrace_6867396
  have hstable : (prefixWord ++ tailWord_6867396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867396).length < 2 ^ (prefixWord ++ tailWord_6867396).sum := by decide
  have hdescent : baseEnd_6867396 < baseStart_6867396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867425 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_6867425 : Nat := 118140960795 + 6867425 * 2 ^ 59
def prefixEnd_6867425 : Nat := 4983230072969 + 3 ^ 40 * 6867425 * 2
def baseEnd_6867425 : Nat := 1175429961234299633934931

theorem tailTrace_6867425 : CollatzResearch.WordTrace tailWord_6867425 prefixEnd_6867425 1175429961234299633934931 := by
  unfold tailWord_6867425
  simp only [CollatzResearch.WordTrace]
  refine ⟨250475567145499562658731729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166983711430333041772487819 250475567145499562658731729)
  ·
    refine ⟨187856675359124671994048797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250475567145499562658731729 187856675359124671994048797)
    ·
      refine ⟨70446253259671751997768299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187856675359124671994048797 70446253259671751997768299)
      ·
        refine ⟨105669379889507627996652449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70446253259671751997768299 105669379889507627996652449)
        ·
          refine ⟨79252034917130720997489337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105669379889507627996652449 79252034917130720997489337)
          ·
            refine ⟨59439026187848040748117003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79252034917130720997489337 59439026187848040748117003)
            ·
              refine ⟨89158539281772061122175505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59439026187848040748117003 89158539281772061122175505)
              ·
                refine ⟨66868904461329045841631629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89158539281772061122175505 66868904461329045841631629)
                ·
                  refine ⟨25075839172998392190611861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66868904461329045841631629 25075839172998392190611861)
                  ·
                    refine ⟨1175429961234299633934931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25075839172998392190611861 1175429961234299633934931)
                    ·
                      rfl

theorem cell23_6867425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_6867425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867425 prefixEnd_6867425 := by exact prefixLift 6867425
  have htrace : WordTrace (prefixWord ++ tailWord_6867425) baseStart_6867425 baseEnd_6867425 := by
    simpa [prefixWord, tailWord_6867425, baseEnd_6867425] using wordTrace_append hprefix tailTrace_6867425
  have hstable : (prefixWord ++ tailWord_6867425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867425).length < 2 ^ (prefixWord ++ tailWord_6867425).sum := by decide
  have hdescent : baseEnd_6867425 < baseStart_6867425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867432 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6867432 : Nat := 118140960795 + 6867432 * 2 ^ 59
def prefixEnd_6867432 : Nat := 4983230072969 + 3 ^ 40 * 6867432 * 2
def baseEnd_6867432 : Nat := 3526293478067480374417261

theorem tailTrace_6867432 : CollatzResearch.WordTrace tailWord_6867432 prefixEnd_6867432 3526293478067480374417261 := by
  unfold tailWord_6867432
  simp only [CollatzResearch.WordTrace]
  refine ⟨125237911228237101427118275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166983881637649468569491033 125237911228237101427118275)
  ·
    refine ⟨187856866842355652140677413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125237911228237101427118275 187856866842355652140677413)
    ·
      refine ⟨35223162532941684776377015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187856866842355652140677413 35223162532941684776377015)
      ·
        refine ⟨52834743799412527164565523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35223162532941684776377015 52834743799412527164565523)
        ·
          refine ⟨79252115699118790746848285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52834743799412527164565523 79252115699118790746848285)
          ·
            refine ⟨29719543387169546530068107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79252115699118790746848285 29719543387169546530068107)
            ·
              refine ⟨44579315080754319795102161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29719543387169546530068107 44579315080754319795102161)
              ·
                refine ⟨33434486310565739846326621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44579315080754319795102161 33434486310565739846326621)
                ·
                  refine ⟨12537932366462152442372483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33434486310565739846326621 12537932366462152442372483)
                  ·
                    refine ⟨18806898549693228663558725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12537932366462152442372483 18806898549693228663558725)
                    ·
                      refine ⟨3526293478067480374417261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18806898549693228663558725 3526293478067480374417261)
                      ·
                        rfl

theorem cell23_6867432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6867432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867432 prefixEnd_6867432 := by exact prefixLift 6867432
  have htrace : WordTrace (prefixWord ++ tailWord_6867432) baseStart_6867432 baseEnd_6867432 := by
    simpa [prefixWord, tailWord_6867432, baseEnd_6867432] using wordTrace_append hprefix tailTrace_6867432
  have hstable : (prefixWord ++ tailWord_6867432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867432).length < 2 ^ (prefixWord ++ tailWord_6867432).sum := by decide
  have hdescent : baseEnd_6867432 < baseStart_6867432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867435 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_6867435 : Nat := 118140960795 + 6867435 * 2 ^ 59
def prefixEnd_6867435 : Nat := 4983230072969 + 3 ^ 40 * 6867435 * 2
def baseEnd_6867435 : Nat := 3526295018509443862679747

theorem tailTrace_6867435 : CollatzResearch.WordTrace tailWord_6867435 prefixEnd_6867435 3526295018509443862679747 := by
  unfold tailWord_6867435
  simp only [CollatzResearch.WordTrace]
  refine ⟨250475931875463334366595759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166983954583642222911063839 250475931875463334366595759)
  ·
    refine ⟨375713897813195001549893639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250475931875463334366595759 375713897813195001549893639)
    ·
      refine ⟨563570846719792502324840459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375713897813195001549893639 563570846719792502324840459)
      ·
        refine ⟨845356270079688753487260689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563570846719792502324840459 845356270079688753487260689)
        ·
          refine ⟨634017202559766565115445517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845356270079688753487260689 634017202559766565115445517)
          ·
            refine ⟨237756450959912461918292069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634017202559766565115445517 237756450959912461918292069)
            ·
              refine ⟨44579334554983586609679763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237756450959912461918292069 44579334554983586609679763)
              ·
                refine ⟨66869001832475379914519645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44579334554983586609679763 66869001832475379914519645)
                ·
                  refine ⟨25075875687178267467944867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66869001832475379914519645 25075875687178267467944867)
                  ·
                    refine ⟨37613813530767401201917301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25075875687178267467944867 37613813530767401201917301)
                    ·
                      refine ⟨3526295018509443862679747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37613813530767401201917301 3526295018509443862679747)
                      ·
                        rfl

theorem cell23_6867435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_6867435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867435 prefixEnd_6867435 := by exact prefixLift 6867435
  have htrace : WordTrace (prefixWord ++ tailWord_6867435) baseStart_6867435 baseEnd_6867435 := by
    simpa [prefixWord, tailWord_6867435, baseEnd_6867435] using wordTrace_append hprefix tailTrace_6867435
  have hstable : (prefixWord ++ tailWord_6867435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867435).length < 2 ^ (prefixWord ++ tailWord_6867435).sum := by decide
  have hdescent : baseEnd_6867435 < baseStart_6867435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867449 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 5, 2, 2]
def baseStart_6867449 : Nat := 118140960795 + 6867449 * 2 ^ 59
def prefixEnd_6867449 : Nat := 4983230072969 + 3 ^ 40 * 6867449 * 2
def baseEnd_6867449 : Nat := 3526302207238606807904683

theorem tailTrace_6867449 : CollatzResearch.WordTrace tailWord_6867449 prefixEnd_6867449 3526302207238606807904683 := by
  unfold tailWord_6867449
  simp only [CollatzResearch.WordTrace]
  refine ⟨250476442497412614757605401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166984294998275076505070267 250476442497412614757605401)
  ·
    refine ⟨187857331873059461068204051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250476442497412614757605401 187857331873059461068204051)
    ·
      refine ⟨281785997809589191602306077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187857331873059461068204051 281785997809589191602306077)
      ·
        refine ⟨105669749178595946850864779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281785997809589191602306077 105669749178595946850864779)
        ·
          refine ⟨158504623767893920276297169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105669749178595946850864779 158504623767893920276297169)
          ·
            refine ⟨118878467825920440207222877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158504623767893920276297169 118878467825920440207222877)
            ·
              refine ⟨44579425434720165077708579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118878467825920440207222877 44579425434720165077708579)
              ·
                refine ⟨66869138152080247616562869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44579425434720165077708579 66869138152080247616562869)
                ·
                  refine ⟨6268981701757523214052769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66869138152080247616562869 6268981701757523214052769)
                  ·
                    refine ⟨4701736276318142410539577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268981701757523214052769 4701736276318142410539577)
                    ·
                      refine ⟨3526302207238606807904683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701736276318142410539577 3526302207238606807904683)
                      ·
                        rfl

theorem cell23_6867449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_6867449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867449 prefixEnd_6867449 := by exact prefixLift 6867449
  have htrace : WordTrace (prefixWord ++ tailWord_6867449) baseStart_6867449 baseEnd_6867449 := by
    simpa [prefixWord, tailWord_6867449, baseEnd_6867449] using wordTrace_append hprefix tailTrace_6867449
  have hstable : (prefixWord ++ tailWord_6867449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867449).length < 2 ^ (prefixWord ++ tailWord_6867449).sum := by decide
  have hdescent : baseEnd_6867449 < baseStart_6867449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867463 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 1, 5]
def baseStart_6867463 : Nat := 118140960795 + 6867463 * 2 ^ 59
def prefixEnd_6867463 : Nat := 4983230072969 + 3 ^ 40 * 6867463 * 2
def baseEnd_6867463 : Nat := 1175436465322589917709873

theorem tailTrace_6867463 : CollatzResearch.WordTrace tailWord_6867463 prefixEnd_6867463 1175436465322589917709873 := by
  unfold tailWord_6867463
  simp only [CollatzResearch.WordTrace]
  refine ⟨250476953119361895148615043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166984635412907930099076695 250476953119361895148615043)
  ·
    refine ⟨375715429679042842722922565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250476953119361895148615043 375715429679042842722922565)
    ·
      refine ⟨70446643064820533010547981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375715429679042842722922565 70446643064820533010547981)
      ·
        refine ⟨26417491149307699878955493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70446643064820533010547981 26417491149307699878955493)
        ·
          refine ⟨4953279590495193727304155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26417491149307699878955493 4953279590495193727304155)
          ·
            refine ⟨7429919385742790590956233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953279590495193727304155 7429919385742790590956233)
            ·
              refine ⟨5572439539307092943217175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7429919385742790590956233 5572439539307092943217175)
              ·
                refine ⟨8358659308960639414825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572439539307092943217175 8358659308960639414825763)
                ·
                  refine ⟨12537988963440959122238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8358659308960639414825763 12537988963440959122238645)
                  ·
                    refine ⟨1175436465322589917709873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12537988963440959122238645 1175436465322589917709873)
                    ·
                      rfl

theorem cell23_6867463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_6867463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867463 prefixEnd_6867463 := by exact prefixLift 6867463
  have htrace : WordTrace (prefixWord ++ tailWord_6867463) baseStart_6867463 baseEnd_6867463 := by
    simpa [prefixWord, tailWord_6867463, baseEnd_6867463] using wordTrace_append hprefix tailTrace_6867463
  have hstable : (prefixWord ++ tailWord_6867463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867463).length < 2 ^ (prefixWord ++ tailWord_6867463).sum := by decide
  have hdescent : baseEnd_6867463 < baseStart_6867463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867476 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_6867476 : Nat := 118140960795 + 6867476 * 2 ^ 59
def prefixEnd_6867476 : Nat := 4983230072969 + 3 ^ 40 * 6867476 * 2
def baseEnd_6867476 : Nat := 1175438690405426067422353

theorem tailTrace_6867476 : CollatzResearch.WordTrace tailWord_6867476 prefixEnd_6867476 1175438690405426067422353 := by
  unfold tailWord_6867476
  simp only [CollatzResearch.WordTrace]
  refine ⟨125238713634157399184419141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166984951512209865579225521 125238713634157399184419141)
  ·
    refine ⟨23482258806404512347078589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125238713634157399184419141 23482258806404512347078589)
    ·
      refine ⟨8805847052401692130154471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23482258806404512347078589 8805847052401692130154471)
      ·
        refine ⟨13208770578602538195231707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8805847052401692130154471 13208770578602538195231707)
        ·
          refine ⟨19813155867903807292847561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13208770578602538195231707 19813155867903807292847561)
          ·
            refine ⟨14859866900927855469635671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19813155867903807292847561 14859866900927855469635671)
            ·
              refine ⟨22289800351391783204453507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14859866900927855469635671 22289800351391783204453507)
              ·
                refine ⟨33434700527087674806680261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22289800351391783204453507 33434700527087674806680261)
                ·
                  refine ⟨6269006348828939026252549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33434700527087674806680261 6269006348828939026252549)
                  ·
                    refine ⟨1175438690405426067422353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269006348828939026252549 1175438690405426067422353)
                    ·
                      rfl

theorem cell23_6867476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_6867476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867476 prefixEnd_6867476 := by exact prefixLift 6867476
  have htrace : WordTrace (prefixWord ++ tailWord_6867476) baseStart_6867476 baseEnd_6867476 := by
    simpa [prefixWord, tailWord_6867476, baseEnd_6867476] using wordTrace_append hprefix tailTrace_6867476
  have hstable : (prefixWord ++ tailWord_6867476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867476).length < 2 ^ (prefixWord ++ tailWord_6867476).sum := by decide
  have hdescent : baseEnd_6867476 < baseStart_6867476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867482 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_6867482 : Nat := 118140960795 + 6867482 * 2 ^ 59
def prefixEnd_6867482 : Nat := 4983230072969 + 3 ^ 40 * 6867482 * 2
def baseEnd_6867482 : Nat := 3526319152100205178792031

theorem tailTrace_6867482 : CollatzResearch.WordTrace tailWord_6867482 prefixEnd_6867482 3526319152100205178792031 := by
  unfold tailWord_6867482
  simp only [CollatzResearch.WordTrace]
  refine ⟨62619411526573265348389175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166985097404195374262371133 62619411526573265348389175)
  ·
    refine ⟨93929117289859898022583763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62619411526573265348389175 93929117289859898022583763)
    ·
      refine ⟨140893675934789847033875645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93929117289859898022583763 140893675934789847033875645)
      ·
        refine ⟨52835128475546192637703367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140893675934789847033875645 52835128475546192637703367)
        ·
          refine ⟨79252692713319288956555051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52835128475546192637703367 79252692713319288956555051)
          ·
            refine ⟨118879039069978933434832577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79252692713319288956555051 118879039069978933434832577)
            ·
              refine ⟨89159279302484200076124433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118879039069978933434832577 89159279302484200076124433)
              ·
                refine ⟨66869459476863150057093325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89159279302484200076124433 66869459476863150057093325)
                ·
                  refine ⟨25076047303823681271409997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66869459476863150057093325 25076047303823681271409997)
                  ·
                    refine ⟨9403517738933880476778749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25076047303823681271409997 9403517738933880476778749)
                    ·
                      refine ⟨3526319152100205178792031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9403517738933880476778749 3526319152100205178792031)
                      ·
                        rfl

theorem cell23_6867482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_6867482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867482 prefixEnd_6867482 := by exact prefixLift 6867482
  have htrace : WordTrace (prefixWord ++ tailWord_6867482) baseStart_6867482 baseEnd_6867482 := by
    simpa [prefixWord, tailWord_6867482, baseEnd_6867482] using wordTrace_append hprefix tailTrace_6867482
  have hstable : (prefixWord ++ tailWord_6867482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867482).length < 2 ^ (prefixWord ++ tailWord_6867482).sum := by decide
  have hdescent : baseEnd_6867482 < baseStart_6867482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867496 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6867496 : Nat := 118140960795 + 6867496 * 2 ^ 59
def prefixEnd_6867496 : Nat := 4983230072969 + 3 ^ 40 * 6867496 * 2
def baseEnd_6867496 : Nat := 3526326340829368124016967

theorem tailTrace_6867496 : CollatzResearch.WordTrace tailWord_6867496 prefixEnd_6867496 3526326340829368124016967 := by
  unfold tailWord_6867496
  simp only [CollatzResearch.WordTrace]
  refine ⟨125239078364121170892283171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166985437818828227856377561 125239078364121170892283171)
  ·
    refine ⟨187858617546181756338424757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125239078364121170892283171 187858617546181756338424757)
    ·
      refine ⟨17611745394954539656727321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187858617546181756338424757 17611745394954539656727321)
      ·
        refine ⟨13208809046215904742545491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17611745394954539656727321 13208809046215904742545491)
        ·
          refine ⟨19813213569323857113818237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13208809046215904742545491 19813213569323857113818237)
          ·
            refine ⟨7429955088496446417681839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19813213569323857113818237 7429955088496446417681839)
            ·
              refine ⟨11144932632744669626522759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429955088496446417681839 11144932632744669626522759)
              ·
                refine ⟨16717398949117004439784139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144932632744669626522759 16717398949117004439784139)
                ·
                  refine ⟨25076098423675506659676209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16717398949117004439784139 25076098423675506659676209)
                  ·
                    refine ⟨18807073817756629994757157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25076098423675506659676209 18807073817756629994757157)
                    ·
                      refine ⟨3526326340829368124016967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18807073817756629994757157 3526326340829368124016967)
                      ·
                        rfl

theorem cell23_6867496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6867496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867496 prefixEnd_6867496 := by exact prefixLift 6867496
  have htrace : WordTrace (prefixWord ++ tailWord_6867496) baseStart_6867496 baseEnd_6867496 := by
    simpa [prefixWord, tailWord_6867496, baseEnd_6867496] using wordTrace_append hprefix tailTrace_6867496
  have hstable : (prefixWord ++ tailWord_6867496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867496).length < 2 ^ (prefixWord ++ tailWord_6867496).sum := by decide
  have hdescent : baseEnd_6867496 < baseStart_6867496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867499 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 3]
def baseStart_6867499 : Nat := 118140960795 + 6867499 * 2 ^ 59
def prefixEnd_6867499 : Nat := 4983230072969 + 3 ^ 40 * 6867499 * 2
def baseEnd_6867499 : Nat := 3526327881271331612279453

theorem tailTrace_6867499 : CollatzResearch.WordTrace tailWord_6867499 prefixEnd_6867499 3526327881271331612279453 := by
  unfold tailWord_6867499
  simp only [CollatzResearch.WordTrace]
  refine ⟨250478266147231473296925551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166985510764820982197950367 250478266147231473296925551)
  ·
    refine ⟨375717399220847209945388327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250478266147231473296925551 375717399220847209945388327)
    ·
      refine ⟨563576098831270814918082491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375717399220847209945388327 563576098831270814918082491)
      ·
        refine ⟨845364148246906222377123737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563576098831270814918082491 845364148246906222377123737)
        ·
          refine ⟨634023111185179666782842803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845364148246906222377123737 634023111185179666782842803)
          ·
            refine ⟨951034666777769500174264205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634023111185179666782842803 951034666777769500174264205)
            ·
              refine ⟨356638000041663562565349077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 951034666777769500174264205 356638000041663562565349077)
              ·
                refine ⟨8358703125976489747625369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 356638000041663562565349077 8358703125976489747625369)
                ·
                  refine ⟨6269027344482367310719027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8358703125976489747625369 6269027344482367310719027)
                  ·
                    refine ⟨9403541016723550966078541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6269027344482367310719027 9403541016723550966078541)
                    ·
                      refine ⟨3526327881271331612279453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9403541016723550966078541 3526327881271331612279453)
                      ·
                        rfl

theorem cell23_6867499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 3].length) (baseStart_6867499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867499 prefixEnd_6867499 := by exact prefixLift 6867499
  have htrace : WordTrace (prefixWord ++ tailWord_6867499) baseStart_6867499 baseEnd_6867499 := by
    simpa [prefixWord, tailWord_6867499, baseEnd_6867499] using wordTrace_append hprefix tailTrace_6867499
  have hstable : (prefixWord ++ tailWord_6867499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867499).length < 2 ^ (prefixWord ++ tailWord_6867499).sum := by decide
  have hdescent : baseEnd_6867499 < baseStart_6867499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867552 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_6867552 : Nat := 118140960795 + 6867552 * 2 ^ 59
def prefixEnd_6867552 : Nat := 4983230072969 + 3 ^ 40 * 6867552 * 2
def baseEnd_6867552 : Nat := 3526355095746019904916709

theorem tailTrace_6867552 : CollatzResearch.WordTrace tailWord_6867552 prefixEnd_6867552 3526355095746019904916709 := by
  unfold tailWord_6867552
  simp only [CollatzResearch.WordTrace]
  refine ⟨125240099608019731674302455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166986799477359642232403273 125240099608019731674302455)
  ·
    refine ⟨187860149412029597511453683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125240099608019731674302455 187860149412029597511453683)
    ·
      refine ⟨281790224118044396267180525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187860149412029597511453683 281790224118044396267180525)
      ·
        refine ⟨105671334044266648600192697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281790224118044396267180525 105671334044266648600192697)
        ·
          refine ⟨79253500533199986450144523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105671334044266648600192697 79253500533199986450144523)
          ·
            refine ⟨118880250799799979675216785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79253500533199986450144523 118880250799799979675216785)
            ·
              refine ⟨89160188099849984756412589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118880250799799979675216785 89160188099849984756412589)
              ·
                refine ⟨33435070537443744283654721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89160188099849984756412589 33435070537443744283654721)
                ·
                  refine ⟨25076302903082808212741041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33435070537443744283654721 25076302903082808212741041)
                  ·
                    refine ⟨18807227177312106159555781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25076302903082808212741041 18807227177312106159555781)
                    ·
                      refine ⟨3526355095746019904916709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18807227177312106159555781 3526355095746019904916709)
                      ·
                        rfl

theorem cell23_6867552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_6867552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867552 prefixEnd_6867552 := by exact prefixLift 6867552
  have htrace : WordTrace (prefixWord ++ tailWord_6867552) baseStart_6867552 baseEnd_6867552 := by
    simpa [prefixWord, tailWord_6867552, baseEnd_6867552] using wordTrace_append hprefix tailTrace_6867552
  have hstable : (prefixWord ++ tailWord_6867552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867552).length < 2 ^ (prefixWord ++ tailWord_6867552).sum := by decide
  have hdescent : baseEnd_6867552 < baseStart_6867552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867560 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6867560 : Nat := 118140960795 + 6867560 * 2 ^ 59
def prefixEnd_6867560 : Nat := 4983230072969 + 3 ^ 40 * 6867560 * 2
def baseEnd_6867560 : Nat := 3526359203591255873616673

theorem tailTrace_6867560 : CollatzResearch.WordTrace tailWord_6867560 prefixEnd_6867560 3526359203591255873616673 := by
  unfold tailWord_6867560
  simp only [CollatzResearch.WordTrace]
  refine ⟨125240245500005240357448067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166986994000006987143264089 125240245500005240357448067)
  ·
    refine ⟨187860368250007860536172101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125240245500005240357448067 187860368250007860536172101)
    ·
      refine ⟨35223819046876473850532269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187860368250007860536172101 35223819046876473850532269)
      ·
        refine ⟨13208932142578677693949601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35223819046876473850532269 13208932142578677693949601)
        ·
          refine ⟨9906699106934008270462201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13208932142578677693949601 9906699106934008270462201)
          ·
            refine ⟨7430024330200506202846651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9906699106934008270462201 7430024330200506202846651)
            ·
              refine ⟨11145036495300759304269977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430024330200506202846651 11145036495300759304269977)
              ·
                refine ⟨8358777371475569478202483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11145036495300759304269977 8358777371475569478202483)
                ·
                  refine ⟨12538166057213354217303725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8358777371475569478202483 12538166057213354217303725)
                  ·
                    refine ⟨4701812271455007831488897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12538166057213354217303725 4701812271455007831488897)
                    ·
                      refine ⟨3526359203591255873616673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701812271455007831488897 3526359203591255873616673)
                      ·
                        rfl

theorem cell23_6867560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6867560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867560 prefixEnd_6867560 := by exact prefixLift 6867560
  have htrace : WordTrace (prefixWord ++ tailWord_6867560) baseStart_6867560 baseEnd_6867560 := by
    simpa [prefixWord, tailWord_6867560, baseEnd_6867560] using wordTrace_append hprefix tailTrace_6867560
  have hstable : (prefixWord ++ tailWord_6867560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867560).length < 2 ^ (prefixWord ++ tailWord_6867560).sum := by decide
  have hdescent : baseEnd_6867560 < baseStart_6867560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867562 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_6867562 : Nat := 118140960795 + 6867562 * 2 ^ 59
def prefixEnd_6867562 : Nat := 4983230072969 + 3 ^ 40 * 6867562 * 2
def baseEnd_6867562 : Nat := 391817803394729429532407

theorem tailTrace_6867562 : CollatzResearch.WordTrace tailWord_6867562 prefixEnd_6867562 391817803394729429532407 := by
  unfold tailWord_6867562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62620140986500808764117235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166987042630668823370979293 62620140986500808764117235)
  ·
    refine ⟨93930211479751213146175853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62620140986500808764117235 93930211479751213146175853)
    ·
      refine ⟨35223829304906704929815945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93930211479751213146175853 35223829304906704929815945)
      ·
        refine ⟨26417871978680028697361959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35223829304906704929815945 26417871978680028697361959)
        ·
          refine ⟨39626807968020043046042939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26417871978680028697361959 39626807968020043046042939)
          ·
            refine ⟨59440211952030064569064409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39626807968020043046042939 59440211952030064569064409)
            ·
              refine ⟨44580158964022548426798307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59440211952030064569064409 44580158964022548426798307)
              ·
                refine ⟨66870238446033822640197461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44580158964022548426798307 66870238446033822640197461)
                ·
                  refine ⟨391817803394729429532407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66870238446033822640197461 391817803394729429532407)
                  ·
                    rfl

theorem cell23_6867562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_6867562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867562 prefixEnd_6867562 := by exact prefixLift 6867562
  have htrace : WordTrace (prefixWord ++ tailWord_6867562) baseStart_6867562 baseEnd_6867562 := by
    simpa [prefixWord, tailWord_6867562, baseEnd_6867562] using wordTrace_append hprefix tailTrace_6867562
  have hstable : (prefixWord ++ tailWord_6867562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867562).length < 2 ^ (prefixWord ++ tailWord_6867562).sum := by decide
  have hdescent : baseEnd_6867562 < baseStart_6867562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867573 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6867573 : Nat := 118140960795 + 6867573 * 2 ^ 59
def prefixEnd_6867573 : Nat := 4983230072969 + 3 ^ 40 * 6867573 * 2
def baseEnd_6867573 : Nat := 3526365878839764322754113

theorem tailTrace_6867573 : CollatzResearch.WordTrace tailWord_6867573 prefixEnd_6867573 3526365878839764322754113 := by
  unfold tailWord_6867573
  simp only [CollatzResearch.WordTrace]
  refine ⟨250480965148963383935119373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166987310099308922623412915 250480965148963383935119373)
  ·
    refine ⟨93930361930861268975669765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250480965148963383935119373 93930361930861268975669765)
    ·
      refine ⟨17611942862036487932938081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93930361930861268975669765 17611942862036487932938081)
      ·
        refine ⟨13208957146527365949703561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17611942862036487932938081 13208957146527365949703561)
        ·
          refine ⟨9906717859895524462277671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13208957146527365949703561 9906717859895524462277671)
          ·
            refine ⟨14860076789843286693416507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9906717859895524462277671 14860076789843286693416507)
            ·
              refine ⟨22290115184764930040124761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14860076789843286693416507 22290115184764930040124761)
              ·
                refine ⟨16717586388573697530093571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22290115184764930040124761 16717586388573697530093571)
                ·
                  refine ⟨25076379582860546295140357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16717586388573697530093571 25076379582860546295140357)
                  ·
                    refine ⟨4701821171786352430338817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25076379582860546295140357 4701821171786352430338817)
                    ·
                      refine ⟨3526365878839764322754113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701821171786352430338817 3526365878839764322754113)
                      ·
                        rfl

theorem cell23_6867573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6867573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867573 prefixEnd_6867573 := by exact prefixLift 6867573
  have htrace : WordTrace (prefixWord ++ tailWord_6867573) baseStart_6867573 baseEnd_6867573 := by
    simpa [prefixWord, tailWord_6867573, baseEnd_6867573] using wordTrace_append hprefix tailTrace_6867573
  have hstable : (prefixWord ++ tailWord_6867573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867573).length < 2 ^ (prefixWord ++ tailWord_6867573).sum := by decide
  have hdescent : baseEnd_6867573 < baseStart_6867573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867642 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_6867642 : Nat := 118140960795 + 6867642 * 2 ^ 59
def prefixEnd_6867642 : Nat := 4983230072969 + 3 ^ 40 * 6867642 * 2
def baseEnd_6867642 : Nat := 3526401309004924552791295

theorem tailTrace_6867642 : CollatzResearch.WordTrace tailWord_6867642 prefixEnd_6867642 3526401309004924552791295 := by
  unfold tailWord_6867642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62620870446428352179845295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166988987857142272479587453 62620870446428352179845295)
  ·
    refine ⟨93931305669642528269767943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62620870446428352179845295 93931305669642528269767943)
    ·
      refine ⟨140896958504463792404651915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93931305669642528269767943 140896958504463792404651915)
      ·
        refine ⟨211345437756695688606977873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140896958504463792404651915 211345437756695688606977873)
        ·
          refine ⟨158509078317521766455233405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211345437756695688606977873 158509078317521766455233405)
          ·
            refine ⟨59440904369070662420712527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158509078317521766455233405 59440904369070662420712527)
            ·
              refine ⟨89161356553605993631068791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59440904369070662420712527 89161356553605993631068791)
              ·
                refine ⟨133742034830408990446603187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89161356553605993631068791 133742034830408990446603187)
                ·
                  refine ⟨200613052245613485669904781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133742034830408990446603187 200613052245613485669904781)
                  ·
                    refine ⟨75229894592105057126214293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 200613052245613485669904781 75229894592105057126214293)
                    ·
                      refine ⟨3526401309004924552791295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75229894592105057126214293 3526401309004924552791295)
                      ·
                        rfl

theorem cell23_6867642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_6867642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867642 prefixEnd_6867642 := by exact prefixLift 6867642
  have htrace : WordTrace (prefixWord ++ tailWord_6867642) baseStart_6867642 baseEnd_6867642 := by
    simpa [prefixWord, tailWord_6867642, baseEnd_6867642] using wordTrace_append hprefix tailTrace_6867642
  have hstable : (prefixWord ++ tailWord_6867642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867642).length < 2 ^ (prefixWord ++ tailWord_6867642).sum := by decide
  have hdescent : baseEnd_6867642 < baseStart_6867642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867646 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_6867646 : Nat := 118140960795 + 6867646 * 2 ^ 59
def prefixEnd_6867646 : Nat := 4983230072969 + 3 ^ 40 * 6867646 * 2
def baseEnd_6867646 : Nat := 3526403362927542537141277

theorem tailTrace_6867646 : CollatzResearch.WordTrace tailWord_6867646 prefixEnd_6867646 3526403362927542537141277 := by
  unfold tailWord_6867646
  simp only [CollatzResearch.WordTrace]
  refine ⟨31310453459712364675315849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166989085118465944935017861 31310453459712364675315849)
  ·
    refine ⟨23482840094784273506486887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31310453459712364675315849 23482840094784273506486887)
    ·
      refine ⟨35224260142176410259730331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23482840094784273506486887 35224260142176410259730331)
      ·
        refine ⟨52836390213264615389595497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35224260142176410259730331 52836390213264615389595497)
        ·
          refine ⟨39627292659948461542196623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52836390213264615389595497 39627292659948461542196623)
          ·
            refine ⟨59440938989922692313294935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39627292659948461542196623 59440938989922692313294935)
            ·
              refine ⟨89161408484884038469942403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59440938989922692313294935 89161408484884038469942403)
              ·
                refine ⟨133742112727326057704913605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89161408484884038469942403 133742112727326057704913605)
                ·
                  refine ⟨25076646136373635819671301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133742112727326057704913605 25076646136373635819671301)
                  ·
                    refine ⟨4701871150570056716188369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25076646136373635819671301 4701871150570056716188369)
                    ·
                      refine ⟨3526403362927542537141277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701871150570056716188369 3526403362927542537141277)
                      ·
                        rfl

theorem cell23_6867646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_6867646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867646 prefixEnd_6867646 := by exact prefixLift 6867646
  have htrace : WordTrace (prefixWord ++ tailWord_6867646) baseStart_6867646 baseEnd_6867646 := by
    simpa [prefixWord, tailWord_6867646, baseEnd_6867646] using wordTrace_append hprefix tailTrace_6867646
  have hstable : (prefixWord ++ tailWord_6867646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867646).length < 2 ^ (prefixWord ++ tailWord_6867646).sum := by decide
  have hdescent : baseEnd_6867646 < baseStart_6867646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867656 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_6867656 : Nat := 118140960795 + 6867656 * 2 ^ 59
def prefixEnd_6867656 : Nat := 4983230072969 + 3 ^ 40 * 6867656 * 2
def baseEnd_6867656 : Nat := 1175469499244695832672077

theorem tailTrace_6867656 : CollatzResearch.WordTrace tailWord_6867656 prefixEnd_6867656 1175469499244695832672077 := by
  unfold tailWord_6867656
  simp only [CollatzResearch.WordTrace]
  refine ⟨125241996203831344555195411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166989328271775126073593881 125241996203831344555195411)
  ·
    refine ⟨187862994305747016832793117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125241996203831344555195411 187862994305747016832793117)
    ·
      refine ⟨70448622864655131312297419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187862994305747016832793117 70448622864655131312297419)
      ·
        refine ⟨105672934296982696968446129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70448622864655131312297419 105672934296982696968446129)
        ·
          refine ⟨79254700722737022726334597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105672934296982696968446129 79254700722737022726334597)
          ·
            refine ⟨14860256385513191761187737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79254700722737022726334597 14860256385513191761187737)
            ·
              refine ⟨11145192289134893820890803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14860256385513191761187737 11145192289134893820890803)
              ·
                refine ⟨16717788433702340731336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145192289134893820890803 16717788433702340731336205)
                ·
                  refine ⟨6269170662638377774251077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16717788433702340731336205 6269170662638377774251077)
                  ·
                    refine ⟨1175469499244695832672077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269170662638377774251077 1175469499244695832672077)
                    ·
                      rfl

theorem cell23_6867656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_6867656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867656 prefixEnd_6867656 := by exact prefixLift 6867656
  have htrace : WordTrace (prefixWord ++ tailWord_6867656) baseStart_6867656 baseEnd_6867656 := by
    simpa [prefixWord, tailWord_6867656, baseEnd_6867656] using wordTrace_append hprefix tailTrace_6867656
  have hstable : (prefixWord ++ tailWord_6867656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867656).length < 2 ^ (prefixWord ++ tailWord_6867656).sum := by decide
  have hdescent : baseEnd_6867656 < baseStart_6867656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867706 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_6867706 : Nat := 118140960795 + 6867706 * 2 ^ 59
def prefixEnd_6867706 : Nat := 4983230072969 + 3 ^ 40 * 6867706 * 2
def baseEnd_6867706 : Nat := 3526434171766812302391001

theorem tailTrace_6867706 : CollatzResearch.WordTrace tailWord_6867706 prefixEnd_6867706 3526434171766812302391001 := by
  unfold tailWord_6867706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62621454014370386912427743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166990544038321031766473981 62621454014370386912427743)
  ·
    refine ⟨93932181021555580368641615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62621454014370386912427743 93932181021555580368641615)
    ·
      refine ⟨140898271532333370552962423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93932181021555580368641615 140898271532333370552962423)
      ·
        refine ⟨211347407298500055829443635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140898271532333370552962423 211347407298500055829443635)
        ·
          refine ⟨317021110947750083744165453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211347407298500055829443635 317021110947750083744165453)
          ·
            refine ⟨118882916605406281404062045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317021110947750083744165453 118882916605406281404062045)
            ·
              refine ⟨44581093727027355526523267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118882916605406281404062045 44581093727027355526523267)
              ·
                refine ⟨66871640590541033289784901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44581093727027355526523267 66871640590541033289784901)
                ·
                  refine ⟨12538432610726443741834669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66871640590541033289784901 12538432610726443741834669)
                  ·
                    refine ⟨4701912229022416403188001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12538432610726443741834669 4701912229022416403188001)
                    ·
                      refine ⟨3526434171766812302391001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701912229022416403188001 3526434171766812302391001)
                      ·
                        rfl

theorem cell23_6867706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_6867706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867706 prefixEnd_6867706 := by exact prefixLift 6867706
  have htrace : WordTrace (prefixWord ++ tailWord_6867706) baseStart_6867706 baseEnd_6867706 := by
    simpa [prefixWord, tailWord_6867706, baseEnd_6867706] using wordTrace_append hprefix tailTrace_6867706
  have hstable : (prefixWord ++ tailWord_6867706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867706).length < 2 ^ (prefixWord ++ tailWord_6867706).sum := by decide
  have hdescent : baseEnd_6867706 < baseStart_6867706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867712 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_6867712 : Nat := 118140960795 + 6867712 * 2 ^ 59
def prefixEnd_6867712 : Nat := 4983230072969 + 3 ^ 40 * 6867712 * 2
def baseEnd_6867712 : Nat := 1175479084216913092971991

theorem tailTrace_6867712 : CollatzResearch.WordTrace tailWord_6867712 prefixEnd_6867712 1175479084216913092971991 := by
  unfold tailWord_6867712
  simp only [CollatzResearch.WordTrace]
  refine ⟨125243017447729905337214695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166990689930306540449619593 125243017447729905337214695)
  ·
    refine ⟨187864526171594858005822043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125243017447729905337214695 187864526171594858005822043)
    ·
      refine ⟨281796789257392287008733065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187864526171594858005822043 281796789257392287008733065)
      ·
        refine ⟨211347591943044215256549799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281796789257392287008733065 211347591943044215256549799)
        ·
          refine ⟨317021387914566322884824699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211347591943044215256549799 317021387914566322884824699)
          ·
            refine ⟨475532081871849484327237049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317021387914566322884824699 475532081871849484327237049)
            ·
              refine ⟨356649061403887113245427787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475532081871849484327237049 356649061403887113245427787)
              ·
                refine ⟨534973592105830669868141681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356649061403887113245427787 534973592105830669868141681)
                ·
                  refine ⟨401230194079373002401106261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534973592105830669868141681 401230194079373002401106261)
                  ·
                    refine ⟨1175479084216913092971991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 401230194079373002401106261 1175479084216913092971991)
                    ·
                      rfl

theorem cell23_6867712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_6867712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867712 prefixEnd_6867712 := by exact prefixLift 6867712
  have htrace : WordTrace (prefixWord ++ tailWord_6867712) baseStart_6867712 baseEnd_6867712 := by
    simpa [prefixWord, tailWord_6867712, baseEnd_6867712] using wordTrace_append hprefix tailTrace_6867712
  have hstable : (prefixWord ++ tailWord_6867712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867712).length < 2 ^ (prefixWord ++ tailWord_6867712).sum := by decide
  have hdescent : baseEnd_6867712 < baseStart_6867712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867746 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6867746 : Nat := 118140960795 + 6867746 * 2 ^ 59
def prefixEnd_6867746 : Nat := 4983230072969 + 3 ^ 40 * 6867746 * 2
def baseEnd_6867746 : Nat := 1175484903664330715296939

theorem tailTrace_6867746 : CollatzResearch.WordTrace tailWord_6867746 prefixEnd_6867746 1175484903664330715296939 := by
  unfold tailWord_6867746
  simp only [CollatzResearch.WordTrace]
  refine ⟨62621818744334158620291773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166991516651557756320778061 62621818744334158620291773)
  ·
    refine ⟨23483182029125309482609415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62621818744334158620291773 23483182029125309482609415)
    ·
      refine ⟨35224773043687964223914123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23483182029125309482609415 35224773043687964223914123)
      ·
        refine ⟨52837159565531946335871185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35224773043687964223914123 52837159565531946335871185)
        ·
          refine ⟨39627869674148959751903389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52837159565531946335871185 39627869674148959751903389)
          ·
            refine ⟨14860451127805859906963771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39627869674148959751903389 14860451127805859906963771)
            ·
              refine ⟨22290676691708789860445657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14860451127805859906963771 22290676691708789860445657)
              ·
                refine ⟨16718007518781592395334243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22290676691708789860445657 16718007518781592395334243)
                ·
                  refine ⟨25077011278172388593001365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16718007518781592395334243 25077011278172388593001365)
                  ·
                    refine ⟨1175484903664330715296939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25077011278172388593001365 1175484903664330715296939)
                    ·
                      rfl

theorem cell23_6867746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6867746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867746 prefixEnd_6867746 := by exact prefixLift 6867746
  have htrace : WordTrace (prefixWord ++ tailWord_6867746) baseStart_6867746 baseEnd_6867746 := by
    simpa [prefixWord, tailWord_6867746, baseEnd_6867746] using wordTrace_append hprefix tailTrace_6867746
  have hstable : (prefixWord ++ tailWord_6867746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867746).length < 2 ^ (prefixWord ++ tailWord_6867746).sum := by decide
  have hdescent : baseEnd_6867746 < baseStart_6867746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867763 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 2, 4]
def baseStart_6867763 : Nat := 118140960795 + 6867763 * 2 ^ 59
def prefixEnd_6867763 : Nat := 4983230072969 + 3 ^ 40 * 6867763 * 2
def baseEnd_6867763 : Nat := 1175487813388039526459413

theorem tailTrace_6867763 : CollatzResearch.WordTrace tailWord_6867763 prefixEnd_6867763 1175487813388039526459413 := by
  unfold tailWord_6867763
  simp only [CollatzResearch.WordTrace]
  refine ⟨250487895018275046384535943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166991930012183364256357295 250487895018275046384535943)
  ·
    refine ⟨375731842527412569576803915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250487895018275046384535943 375731842527412569576803915)
    ·
      refine ⟨563597763791118854365205873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375731842527412569576803915 563597763791118854365205873)
      ·
        refine ⟨422698322843339140773904405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563597763791118854365205873 422698322843339140773904405)
        ·
          refine ⟨19813983883281522223776769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 422698322843339140773904405 19813983883281522223776769)
          ·
            refine ⟨14860487912461141667832577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19813983883281522223776769 14860487912461141667832577)
            ·
              refine ⟨11145365934345856250874433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14860487912461141667832577 11145365934345856250874433)
              ·
                refine ⟨8359024450759392188155825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11145365934345856250874433 8359024450759392188155825)
                ·
                  refine ⟨6269268338069544141116869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8359024450759392188155825 6269268338069544141116869)
                  ·
                    refine ⟨1175487813388039526459413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269268338069544141116869 1175487813388039526459413)
                    ·
                      rfl

theorem cell23_6867763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 4].length) (baseStart_6867763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867763 prefixEnd_6867763 := by exact prefixLift 6867763
  have htrace : WordTrace (prefixWord ++ tailWord_6867763) baseStart_6867763 baseEnd_6867763 := by
    simpa [prefixWord, tailWord_6867763, baseEnd_6867763] using wordTrace_append hprefix tailTrace_6867763
  have hstable : (prefixWord ++ tailWord_6867763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867763).length < 2 ^ (prefixWord ++ tailWord_6867763).sum := by decide
  have hdescent : baseEnd_6867763 < baseStart_6867763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867780 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6867780 : Nat := 118140960795 + 6867780 * 2 ^ 59
def prefixEnd_6867780 : Nat := 4983230072969 + 3 ^ 40 * 6867780 * 2
def baseEnd_6867780 : Nat := 1175490723111748337621887

theorem tailTrace_6867780 : CollatzResearch.WordTrace tailWord_6867780 prefixEnd_6867780 1175490723111748337621887 := by
  unfold tailWord_6867780
  simp only [CollatzResearch.WordTrace]
  refine ⟨125244257529606729143952397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166992343372808972191936529 125244257529606729143952397)
  ·
    refine ⟨46966596573602523428982149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125244257529606729143952397 46966596573602523428982149)
    ·
      refine ⟨8806236857550473142934153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46966596573602523428982149 8806236857550473142934153)
      ·
        refine ⟨6604677643162854857200615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8806236857550473142934153 6604677643162854857200615)
        ·
          refine ⟨9907016464744282285800923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604677643162854857200615 9907016464744282285800923)
          ·
            refine ⟨14860524697116423428701385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9907016464744282285800923 14860524697116423428701385)
            ·
              refine ⟨11145393522837317571526039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14860524697116423428701385 11145393522837317571526039)
              ·
                refine ⟨16718090284255976357289059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145393522837317571526039 16718090284255976357289059)
                ·
                  refine ⟨25077135426383964535933589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16718090284255976357289059 25077135426383964535933589)
                  ·
                    refine ⟨1175490723111748337621887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25077135426383964535933589 1175490723111748337621887)
                    ·
                      rfl

theorem cell23_6867780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6867780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867780 prefixEnd_6867780 := by exact prefixLift 6867780
  have htrace : WordTrace (prefixWord ++ tailWord_6867780) baseStart_6867780 baseEnd_6867780 := by
    simpa [prefixWord, tailWord_6867780, baseEnd_6867780] using wordTrace_append hprefix tailTrace_6867780
  have hstable : (prefixWord ++ tailWord_6867780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867780).length < 2 ^ (prefixWord ++ tailWord_6867780).sum := by decide
  have hdescent : baseEnd_6867780 < baseStart_6867780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867804 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6867804 : Nat := 118140960795 + 6867804 * 2 ^ 59
def prefixEnd_6867804 : Nat := 4983230072969 + 3 ^ 40 * 6867804 * 2
def baseEnd_6867804 : Nat := 3526484492870952918965551

theorem tailTrace_6867804 : CollatzResearch.WordTrace tailWord_6867804 prefixEnd_6867804 3526484492870952918965551 := by
  unfold tailWord_6867804
  simp only [CollatzResearch.WordTrace]
  refine ⟨125244695205563255193389233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166992926940751006924518977 125244695205563255193389233)
  ·
    refine ⟨93933521404172441395041925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125244695205563255193389233 93933521404172441395041925)
    ·
      refine ⟨17612535263282332761570361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93933521404172441395041925 17612535263282332761570361)
      ·
        refine ⟨13209401447461749571177771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17612535263282332761570361 13209401447461749571177771)
        ·
          refine ⟨19814102171192624356766657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13209401447461749571177771 19814102171192624356766657)
          ·
            refine ⟨14860576628394468267574993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19814102171192624356766657 14860576628394468267574993)
            ·
              refine ⟨11145432471295851200681245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14860576628394468267574993 11145432471295851200681245)
              ·
                refine ⟨4179537176735944200255467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11145432471295851200681245 4179537176735944200255467)
                ·
                  refine ⟨6269305765103916300383201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179537176735944200255467 6269305765103916300383201)
                  ·
                    refine ⟨4701979323827937225287401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6269305765103916300383201 4701979323827937225287401)
                    ·
                      refine ⟨3526484492870952918965551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4701979323827937225287401 3526484492870952918965551)
                      ·
                        rfl

theorem cell23_6867804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6867804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867804 prefixEnd_6867804 := by exact prefixLift 6867804
  have htrace : WordTrace (prefixWord ++ tailWord_6867804) baseStart_6867804 baseEnd_6867804 := by
    simpa [prefixWord, tailWord_6867804, baseEnd_6867804] using wordTrace_append hprefix tailTrace_6867804
  have hstable : (prefixWord ++ tailWord_6867804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867804).length < 2 ^ (prefixWord ++ tailWord_6867804).sum := by decide
  have hdescent : baseEnd_6867804 < baseStart_6867804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867809 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6867809 : Nat := 118140960795 + 6867809 * 2 ^ 59
def prefixEnd_6867809 : Nat := 4983230072969 + 3 ^ 40 * 6867809 * 2
def baseEnd_6867809 : Nat := 3526487060274225399403027

theorem tailTrace_6867809 : CollatzResearch.WordTrace tailWord_6867809 prefixEnd_6867809 3526487060274225399403027 := by
  unfold tailWord_6867809
  simp only [CollatzResearch.WordTrace]
  refine ⟨250489572776108396240710481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166993048517405597493806987 250489572776108396240710481)
  ·
    refine ⟨187867179582081297180532861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250489572776108396240710481 187867179582081297180532861)
    ·
      refine ⟨70450192343280486442699823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187867179582081297180532861 70450192343280486442699823)
      ·
        refine ⟨105675288514920729664049735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70450192343280486442699823 105675288514920729664049735)
        ·
          refine ⟨158512932772381094496074603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105675288514920729664049735 158512932772381094496074603)
          ·
            refine ⟨237769399158571641744111905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158512932772381094496074603 237769399158571641744111905)
            ·
              refine ⟨178327049368928731308083929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237769399158571641744111905 178327049368928731308083929)
              ·
                refine ⟨133745287026696548481062947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178327049368928731308083929 133745287026696548481062947)
                ·
                  refine ⟨200617930540044822721594421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133745287026696548481062947 200617930540044822721594421)
                  ·
                    refine ⟨18807930988129202130149477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200617930540044822721594421 18807930988129202130149477)
                    ·
                      refine ⟨3526487060274225399403027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18807930988129202130149477 3526487060274225399403027)
                      ·
                        rfl

theorem cell23_6867809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6867809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867809 prefixEnd_6867809 := by exact prefixLift 6867809
  have htrace : WordTrace (prefixWord ++ tailWord_6867809) baseStart_6867809 baseEnd_6867809 := by
    simpa [prefixWord, tailWord_6867809, baseEnd_6867809] using wordTrace_append hprefix tailTrace_6867809
  have hstable : (prefixWord ++ tailWord_6867809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867809).length < 2 ^ (prefixWord ++ tailWord_6867809).sum := by decide
  have hdescent : baseEnd_6867809 < baseStart_6867809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867819 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 2, 6]
def baseStart_6867819 : Nat := 118140960795 + 6867819 * 2 ^ 59
def prefixEnd_6867819 : Nat := 4983230072969 + 3 ^ 40 * 6867819 * 2
def baseEnd_6867819 : Nat := 1175497398360256786759327

theorem tailTrace_6867819 : CollatzResearch.WordTrace tailWord_6867819 prefixEnd_6867819 1175497398360256786759327 := by
  unfold tailWord_6867819
  simp only [CollatzResearch.WordTrace]
  refine ⟨250489937506072167948574511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166993291670714778632383007 250489937506072167948574511)
  ·
    refine ⟨375734906259108251922861767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250489937506072167948574511 375734906259108251922861767)
    ·
      refine ⟨563602359388662377884292651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375734906259108251922861767 563602359388662377884292651)
      ·
        refine ⟨845403539082993566826438977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563602359388662377884292651 845403539082993566826438977)
        ·
          refine ⟨634052654312245175119829233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845403539082993566826438977 634052654312245175119829233)
          ·
            refine ⟨475539490734183881339871925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634052654312245175119829233 475539490734183881339871925)
            ·
              refine ⟨44581827256329738875612993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 475539490734183881339871925 44581827256329738875612993)
              ·
                refine ⟨33436370442247304156709745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44581827256329738875612993 33436370442247304156709745)
                ·
                  refine ⟨25077277831685478117532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33436370442247304156709745 25077277831685478117532309)
                  ·
                    refine ⟨1175497398360256786759327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25077277831685478117532309 1175497398360256786759327)
                    ·
                      rfl

theorem cell23_6867819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_6867819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867819 prefixEnd_6867819 := by exact prefixLift 6867819
  have htrace : WordTrace (prefixWord ++ tailWord_6867819) baseStart_6867819 baseEnd_6867819 := by
    simpa [prefixWord, tailWord_6867819, baseEnd_6867819] using wordTrace_append hprefix tailTrace_6867819
  have hstable : (prefixWord ++ tailWord_6867819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867819).length < 2 ^ (prefixWord ++ tailWord_6867819).sum := by decide
  have hdescent : baseEnd_6867819 < baseStart_6867819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867860 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6867860 : Nat := 118140960795 + 6867860 * 2 ^ 59
def prefixEnd_6867860 : Nat := 4983230072969 + 3 ^ 40 * 6867860 * 2
def baseEnd_6867860 : Nat := 3526513247787604699865293

theorem tailTrace_6867860 : CollatzResearch.WordTrace tailWord_6867860 prefixEnd_6867860 3526513247787604699865293 := by
  unfold tailWord_6867860
  simp only [CollatzResearch.WordTrace]
  refine ⟨125245716449461815975408517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166994288599282421300544689 125245716449461815975408517)
  ·
    refine ⟨23483571834274090495389097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125245716449461815975408517 23483571834274090495389097)
    ·
      refine ⟨17612678875705567871541823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23483571834274090495389097 17612678875705567871541823)
      ·
        refine ⟨26419018313558351807312735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17612678875705567871541823 26419018313558351807312735)
        ·
          refine ⟨39628527470337527710969103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26419018313558351807312735 39628527470337527710969103)
          ·
            refine ⟨59442791205506291566453655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39628527470337527710969103 59442791205506291566453655)
            ·
              refine ⟨89164186808259437349680483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59442791205506291566453655 89164186808259437349680483)
              ·
                refine ⟨133746280212389156024520725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89164186808259437349680483 133746280212389156024520725)
                ·
                  refine ⟨6269356884955741688649409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133746280212389156024520725 6269356884955741688649409)
                  ·
                    refine ⟨4702017663716806266487057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6269356884955741688649409 4702017663716806266487057)
                    ·
                      refine ⟨3526513247787604699865293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702017663716806266487057 3526513247787604699865293)
                      ·
                        rfl

theorem cell23_6867860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6867860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867860 prefixEnd_6867860 := by exact prefixLift 6867860
  have htrace : WordTrace (prefixWord ++ tailWord_6867860) baseStart_6867860 baseEnd_6867860 := by
    simpa [prefixWord, tailWord_6867860, baseEnd_6867860] using wordTrace_append hprefix tailTrace_6867860
  have hstable : (prefixWord ++ tailWord_6867860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867860).length < 2 ^ (prefixWord ++ tailWord_6867860).sum := by decide
  have hdescent : baseEnd_6867860 < baseStart_6867860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6867936 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_6867936 : Nat := 118140960795 + 6867936 * 2 ^ 59
def prefixEnd_6867936 : Nat := 4983230072969 + 3 ^ 40 * 6867936 * 2
def baseEnd_6867936 : Nat := 3526552272317346402514943

theorem tailTrace_6867936 : CollatzResearch.WordTrace tailWord_6867936 prefixEnd_6867936 3526552272317346402514943 := by
  unfold tailWord_6867936
  simp only [CollatzResearch.WordTrace]
  refine ⟨125247102423324148465291831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166996136564432197953722441 125247102423324148465291831)
  ·
    refine ⟨187870653634986222697937747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125247102423324148465291831 187870653634986222697937747)
    ·
      refine ⟨281805980452479334046906621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187870653634986222697937747 281805980452479334046906621)
      ·
        refine ⟨105677242669679750267589983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281805980452479334046906621 105677242669679750267589983)
        ·
          refine ⟨158515864004519625401384975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105677242669679750267589983 158515864004519625401384975)
          ·
            refine ⟨237773796006779438102077463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158515864004519625401384975 237773796006779438102077463)
            ·
              refine ⟨356660694010169157153116195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237773796006779438102077463 356660694010169157153116195)
              ·
                refine ⟨534991041015253735729674293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356660694010169157153116195 534991041015253735729674293)
                ·
                  refine ⟨50155410095180037724656965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534991041015253735729674293 50155410095180037724656965)
                  ·
                    refine ⟨9404139392846257073373181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50155410095180037724656965 9404139392846257073373181)
                    ·
                      refine ⟨3526552272317346402514943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9404139392846257073373181 3526552272317346402514943)
                      ·
                        rfl

theorem cell23_6867936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_6867936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6867936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6867936 prefixEnd_6867936 := by exact prefixLift 6867936
  have htrace : WordTrace (prefixWord ++ tailWord_6867936) baseStart_6867936 baseEnd_6867936 := by
    simpa [prefixWord, tailWord_6867936, baseEnd_6867936] using wordTrace_append hprefix tailTrace_6867936
  have hstable : (prefixWord ++ tailWord_6867936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6867936).length < 2 ^ (prefixWord ++ tailWord_6867936).sum := by decide
  have hdescent : baseEnd_6867936 < baseStart_6867936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6867936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868007 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 6]
def baseStart_6868007 : Nat := 118140960795 + 6868007 * 2 ^ 59
def prefixEnd_6868007 : Nat := 4983230072969 + 3 ^ 40 * 6868007 * 2
def baseEnd_6868007 : Nat := 391843192160423958303013

theorem tailTrace_6868007 : CollatzResearch.WordTrace tailWord_6868007 prefixEnd_6868007 391843192160423958303013 := by
  unfold tailWord_6868007
  simp only [CollatzResearch.WordTrace]
  refine ⟨250496794429391076056418275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166997862952927384037612183 250496794429391076056418275)
  ·
    refine ⟨375745191644086614084627413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250496794429391076056418275 375745191644086614084627413)
    ·
      refine ⟨8806527929158280017608455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 375745191644086614084627413 8806527929158280017608455)
      ·
        refine ⟨13209791893737420026412683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8806527929158280017608455 13209791893737420026412683)
        ·
          refine ⟨19814687840606130039619025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13209791893737420026412683 19814687840606130039619025)
          ·
            refine ⟨14861015880454597529714269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19814687840606130039619025 14861015880454597529714269)
            ·
              refine ⟨5572880955170474073642851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14861015880454597529714269 5572880955170474073642851)
              ·
                refine ⟨8359321432755711110464277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572880955170474073642851 8359321432755711110464277)
                ·
                  refine ⟨391843192160423958303013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8359321432755711110464277 391843192160423958303013)
                  ·
                    rfl

theorem cell23_6868007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 6].length) (baseStart_6868007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868007 prefixEnd_6868007 := by exact prefixLift 6868007
  have htrace : WordTrace (prefixWord ++ tailWord_6868007) baseStart_6868007 baseEnd_6868007 := by
    simpa [prefixWord, tailWord_6868007, baseEnd_6868007] using wordTrace_append hprefix tailTrace_6868007
  have hstable : (prefixWord ++ tailWord_6868007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868007).length < 2 ^ (prefixWord ++ tailWord_6868007).sum := by decide
  have hdescent : baseEnd_6868007 < baseStart_6868007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868023 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_6868023 : Nat := 118140960795 + 6868023 * 2 ^ 59
def prefixEnd_6868023 : Nat := 4983230072969 + 3 ^ 40 * 6868023 * 2
def baseEnd_6868023 : Nat := 3526596945134287562127043

theorem tailTrace_6868023 : CollatzResearch.WordTrace tailWord_6868023 prefixEnd_6868023 3526596945134287562127043 := by
  unfold tailWord_6868023
  simp only [CollatzResearch.WordTrace]
  refine ⟨250497377997333110789000723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166998251998222073859333815 250497377997333110789000723)
  ·
    refine ⟨375746066995999666183501085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250497377997333110789000723 375746066995999666183501085)
    ·
      refine ⟨140904775123499874818812907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375746066995999666183501085 140904775123499874818812907)
      ·
        refine ⟨211357162685249812228219361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140904775123499874818812907 211357162685249812228219361)
        ·
          refine ⟨158517872013937359171164521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211357162685249812228219361 158517872013937359171164521)
          ·
            refine ⟨118888404010453019378373391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158517872013937359171164521 118888404010453019378373391)
            ·
              refine ⟨178332606015679529067560087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118888404010453019378373391 178332606015679529067560087)
              ·
                refine ⟨267498909023519293601340131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178332606015679529067560087 267498909023519293601340131)
                ·
                  refine ⟨401248363535278940402010197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267498909023519293601340131 401248363535278940402010197)
                  ·
                    refine ⟨4702129260179050082836057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 401248363535278940402010197 4702129260179050082836057)
                    ·
                      refine ⟨3526596945134287562127043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702129260179050082836057 3526596945134287562127043)
                      ·
                        rfl

theorem cell23_6868023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_6868023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868023 prefixEnd_6868023 := by exact prefixLift 6868023
  have htrace : WordTrace (prefixWord ++ tailWord_6868023) baseStart_6868023 baseEnd_6868023 := by
    simpa [prefixWord, tailWord_6868023, baseEnd_6868023] using wordTrace_append hprefix tailTrace_6868023
  have hstable : (prefixWord ++ tailWord_6868023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868023).length < 2 ^ (prefixWord ++ tailWord_6868023).sum := by decide
  have hdescent : baseEnd_6868023 < baseStart_6868023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868050 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_6868050 : Nat := 118140960795 + 6868050 * 2 ^ 59
def prefixEnd_6868050 : Nat := 4983230072969 + 3 ^ 40 * 6868050 * 2
def baseEnd_6868050 : Nat := 1175536936370652985496473

theorem tailTrace_6868050 : CollatzResearch.WordTrace tailWord_6868050 prefixEnd_6868050 1175536936370652985496473 := by
  unfold tailWord_6868050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62624590692058823600058401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166998908512156862933489069 62624590692058823600058401)
  ·
    refine ⟨46968443019044117700043801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62624590692058823600058401 46968443019044117700043801)
    ·
      refine ⟨35226332264283088275032851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46968443019044117700043801 35226332264283088275032851)
      ·
        refine ⟨52839498396424632412549277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35226332264283088275032851 52839498396424632412549277)
        ·
          refine ⟨19814811898659237154705979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52839498396424632412549277 19814811898659237154705979)
          ·
            refine ⟨29722217847988855732058969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19814811898659237154705979 29722217847988855732058969)
            ·
              refine ⟨22291663385991641799044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29722217847988855732058969 22291663385991641799044227)
              ·
                refine ⟨33437495078987462698566341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22291663385991641799044227 33437495078987462698566341)
                ·
                  refine ⟨6269530327310149255981189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33437495078987462698566341 6269530327310149255981189)
                  ·
                    refine ⟨1175536936370652985496473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269530327310149255981189 1175536936370652985496473)
                    ·
                      rfl

theorem cell23_6868050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_6868050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868050 prefixEnd_6868050 := by exact prefixLift 6868050
  have htrace : WordTrace (prefixWord ++ tailWord_6868050) baseStart_6868050 baseEnd_6868050 := by
    simpa [prefixWord, tailWord_6868050, baseEnd_6868050] using wordTrace_append hprefix tailTrace_6868050
  have hstable : (prefixWord ++ tailWord_6868050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868050).length < 2 ^ (prefixWord ++ tailWord_6868050).sum := by decide
  have hdescent : baseEnd_6868050 < baseStart_6868050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868060 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6868060 : Nat := 118140960795 + 6868060 * 2 ^ 59
def prefixEnd_6868060 : Nat := 4983230072969 + 3 ^ 40 * 6868060 * 2
def baseEnd_6868060 : Nat := 3526615943918503917364373

theorem tailTrace_6868060 : CollatzResearch.WordTrace tailWord_6868060 prefixEnd_6868060 3526615943918503917364373 := by
  unfold tailWord_6868060
  simp only [CollatzResearch.WordTrace]
  refine ⟨125249363749099533054048817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166999151665466044072065089 125249363749099533054048817)
  ·
    refine ⟨93937022811824649790536613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125249363749099533054048817 93937022811824649790536613)
    ·
      refine ⟨17613191777217121835725615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93937022811824649790536613 17613191777217121835725615)
      ·
        refine ⟨26419787665825682753588423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17613191777217121835725615 26419787665825682753588423)
        ·
          refine ⟨39629681498738524130382635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26419787665825682753588423 39629681498738524130382635)
          ·
            refine ⟨59444522248107786195573953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39629681498738524130382635 59444522248107786195573953)
            ·
              refine ⟨44583391686080839646680465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59444522248107786195573953 44583391686080839646680465)
              ·
                refine ⟨33437543764560629735010349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44583391686080839646680465 33437543764560629735010349)
                ·
                  refine ⟨12539078911710236150628881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33437543764560629735010349 12539078911710236150628881)
                  ·
                    refine ⟨9404309183782677112971661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12539078911710236150628881 9404309183782677112971661)
                    ·
                      refine ⟨3526615943918503917364373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9404309183782677112971661 3526615943918503917364373)
                      ·
                        rfl

theorem cell23_6868060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6868060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868060 prefixEnd_6868060 := by exact prefixLift 6868060
  have htrace : WordTrace (prefixWord ++ tailWord_6868060) baseStart_6868060 baseEnd_6868060 := by
    simpa [prefixWord, tailWord_6868060, baseEnd_6868060] using wordTrace_append hprefix tailTrace_6868060
  have hstable : (prefixWord ++ tailWord_6868060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868060).length < 2 ^ (prefixWord ++ tailWord_6868060).sum := by decide
  have hdescent : baseEnd_6868060 < baseStart_6868060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868077 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_6868077 : Nat := 118140960795 + 6868077 * 2 ^ 59
def prefixEnd_6868077 : Nat := 4983230072969 + 3 ^ 40 * 6868077 * 2
def baseEnd_6868077 : Nat := 3526624673089630350851795

theorem tailTrace_6868077 : CollatzResearch.WordTrace tailWord_6868077 prefixEnd_6868077 3526624673089630350851795 := by
  unfold tailWord_6868077
  simp only [CollatzResearch.WordTrace]
  refine ⟨250499347539137478011466485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166999565026091652007644323 250499347539137478011466485)
  ·
    refine ⟨23484313831794138563574983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250499347539137478011466485 23484313831794138563574983)
    ·
      refine ⟨35226470747691207845362475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23484313831794138563574983 35226470747691207845362475)
      ·
        refine ⟨52839706121536811768043713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35226470747691207845362475 52839706121536811768043713)
        ·
          refine ⟨39629779591152608826032785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52839706121536811768043713 39629779591152608826032785)
          ·
            refine ⟨29722334693364456619524589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39629779591152608826032785 29722334693364456619524589)
            ·
              refine ⟨11145875510011671232321721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29722334693364456619524589 11145875510011671232321721)
              ·
                refine ⟨8359406632508753424241291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11145875510011671232321721 8359406632508753424241291)
                ·
                  refine ⟨12539109948763130136361937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359406632508753424241291 12539109948763130136361937)
                  ·
                    refine ⟨9404332461572347602271453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12539109948763130136361937 9404332461572347602271453)
                    ·
                      refine ⟨3526624673089630350851795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9404332461572347602271453 3526624673089630350851795)
                      ·
                        rfl

theorem cell23_6868077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_6868077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868077 prefixEnd_6868077 := by exact prefixLift 6868077
  have htrace : WordTrace (prefixWord ++ tailWord_6868077) baseStart_6868077 baseEnd_6868077 := by
    simpa [prefixWord, tailWord_6868077, baseEnd_6868077] using wordTrace_append hprefix tailTrace_6868077
  have hstable : (prefixWord ++ tailWord_6868077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868077).length < 2 ^ (prefixWord ++ tailWord_6868077).sum := by decide
  have hdescent : baseEnd_6868077 < baseStart_6868077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868170 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_6868170 : Nat := 118140960795 + 6868170 * 2 ^ 59
def prefixEnd_6868170 : Nat := 4983230072969 + 3 ^ 40 * 6868170 * 2
def baseEnd_6868170 : Nat := 391852491865610942998763

theorem tailTrace_6868170 : CollatzResearch.WordTrace tailWord_6868170 prefixEnd_6868170 391852491865610942998763 := by
  unfold tailWord_6868170
  simp only [CollatzResearch.WordTrace]
  refine ⟨62625684881950138723650491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167001826351867036596401309 62625684881950138723650491)
  ·
    refine ⟨93938527322925208085475737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62625684881950138723650491 93938527322925208085475737)
    ·
      refine ⟨70453895492193906064106803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93938527322925208085475737 70453895492193906064106803)
      ·
        refine ⟨105680843238290859096160205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70453895492193906064106803 105680843238290859096160205)
        ·
          refine ⟨39630316214359072161060077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105680843238290859096160205 39630316214359072161060077)
          ·
            refine ⟨14861368580384652060397529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39630316214359072161060077 14861368580384652060397529)
            ·
              refine ⟨11146026435288489045298147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14861368580384652060397529 11146026435288489045298147)
              ·
                refine ⟨16719039652932733567947221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146026435288489045298147 16719039652932733567947221)
                ·
                  refine ⟨391852491865610942998763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16719039652932733567947221 391852491865610942998763)
                  ·
                    rfl

theorem cell23_6868170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_6868170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868170 prefixEnd_6868170 := by exact prefixLift 6868170
  have htrace : WordTrace (prefixWord ++ tailWord_6868170) baseStart_6868170 baseEnd_6868170 := by
    simpa [prefixWord, tailWord_6868170, baseEnd_6868170] using wordTrace_append hprefix tailTrace_6868170
  have hstable : (prefixWord ++ tailWord_6868170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868170).length < 2 ^ (prefixWord ++ tailWord_6868170).sum := by decide
  have hdescent : baseEnd_6868170 < baseStart_6868170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868183 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 7]
def baseStart_6868183 : Nat := 118140960795 + 6868183 * 2 ^ 59
def prefixEnd_6868183 : Nat := 4983230072969 + 3 ^ 40 * 6868183 * 2
def baseEnd_6868183 : Nat := 1175559700679668978708769

theorem tailTrace_6868183 : CollatzResearch.WordTrace tailWord_6868183 prefixEnd_6868183 1175559700679668978708769 := by
  unfold tailWord_6868183
  simp only [CollatzResearch.WordTrace]
  refine ⟨250503213676753458114825203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167002142451168972076550135 250503213676753458114825203)
  ·
    refine ⟨375754820515130187172237805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250503213676753458114825203 375754820515130187172237805)
    ·
      refine ⟨140908057693173820189589177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375754820515130187172237805 140908057693173820189589177)
      ·
        refine ⟨105681043269880365142191883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140908057693173820189589177 105681043269880365142191883)
        ·
          refine ⟨158521564904820547713287825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105681043269880365142191883 158521564904820547713287825)
          ·
            refine ⟨118891173678615410784965869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158521564904820547713287825 118891173678615410784965869)
            ·
              refine ⟨44584190129480779044362201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118891173678615410784965869 44584190129480779044362201)
              ·
                refine ⟨33438142597110584283271651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44584190129480779044362201 33438142597110584283271651)
                ·
                  refine ⟨50157213895665876424907477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33438142597110584283271651 50157213895665876424907477)
                  ·
                    refine ⟨1175559700679668978708769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50157213895665876424907477 1175559700679668978708769)
                    ·
                      rfl

theorem cell23_6868183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_6868183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868183 prefixEnd_6868183 := by exact prefixLift 6868183
  have htrace : WordTrace (prefixWord ++ tailWord_6868183) baseStart_6868183 baseEnd_6868183 := by
    simpa [prefixWord, tailWord_6868183, baseEnd_6868183] using wordTrace_append hprefix tailTrace_6868183
  have hstable : (prefixWord ++ tailWord_6868183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868183).length < 2 ^ (prefixWord ++ tailWord_6868183).sum := by decide
  have hdescent : baseEnd_6868183 < baseStart_6868183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868200 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6868200 : Nat := 118140960795 + 6868200 * 2 ^ 59
def prefixEnd_6868200 : Nat := 4983230072969 + 3 ^ 40 * 6868200 * 2
def baseEnd_6868200 : Nat := 1175562610403377789871243

theorem tailTrace_6868200 : CollatzResearch.WordTrace tailWord_6868200 prefixEnd_6868200 1175562610403377789871243 := by
  unfold tailWord_6868200
  simp only [CollatzResearch.WordTrace]
  refine ⟨125251916858845935009097027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167002555811794580012129369 125251916858845935009097027)
  ·
    refine ⟨187877875288268902513645541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125251916858845935009097027 187877875288268902513645541)
    ·
      refine ⟨35227101616550419221308539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187877875288268902513645541 35227101616550419221308539)
      ·
        refine ⟨52840652424825628831962809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35227101616550419221308539 52840652424825628831962809)
        ·
          refine ⟨39630489318619221623972107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52840652424825628831962809 39630489318619221623972107)
          ·
            refine ⟨59445733977928832435958161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39630489318619221623972107 59445733977928832435958161)
            ·
              refine ⟨44584300483446624326968621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59445733977928832435958161 44584300483446624326968621)
              ·
                refine ⟨16719112681292484122613233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44584300483446624326968621 16719112681292484122613233)
                ·
                  refine ⟨12539334510969363091959925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16719112681292484122613233 12539334510969363091959925)
                  ·
                    refine ⟨1175562610403377789871243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12539334510969363091959925 1175562610403377789871243)
                    ·
                      rfl

theorem cell23_6868200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6868200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868200 prefixEnd_6868200 := by exact prefixLift 6868200
  have htrace : WordTrace (prefixWord ++ tailWord_6868200) baseStart_6868200 baseEnd_6868200 := by
    simpa [prefixWord, tailWord_6868200, baseEnd_6868200] using wordTrace_append hprefix tailTrace_6868200
  have hstable : (prefixWord ++ tailWord_6868200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868200).length < 2 ^ (prefixWord ++ tailWord_6868200).sum := by decide
  have hdescent : baseEnd_6868200 < baseStart_6868200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868277 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 6]
def baseStart_6868277 : Nat := 118140960795 + 6868277 * 2 ^ 59
def prefixEnd_6868277 : Nat := 4983230072969 + 3 ^ 40 * 6868277 * 2
def baseEnd_6868277 : Nat := 391858596580058840927875

theorem tailTrace_6868277 : CollatzResearch.WordTrace tailWord_6868277 prefixEnd_6868277 391858596580058840927875 := by
  unfold tailWord_6868277
  simp only [CollatzResearch.WordTrace]
  refine ⟨250506642138412912168747085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167004428092275274779164723 250506642138412912168747085)
  ·
    refine ⟨93939990801904842063280157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250506642138412912168747085 93939990801904842063280157)
    ·
      refine ⟨35227496550714315773730059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93939990801904842063280157 35227496550714315773730059)
      ·
        refine ⟨52841244826071473660595089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35227496550714315773730059 52841244826071473660595089)
        ·
          refine ⟨39630933619553605245446317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52841244826071473660595089 39630933619553605245446317)
          ·
            refine ⟨14861600107332601967042369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39630933619553605245446317 14861600107332601967042369)
            ·
              refine ⟨11146200080499451475281777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14861600107332601967042369 11146200080499451475281777)
              ·
                refine ⟨8359650060374588606461333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11146200080499451475281777 8359650060374588606461333)
                ·
                  refine ⟨391858596580058840927875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8359650060374588606461333 391858596580058840927875)
                  ·
                    rfl

theorem cell23_6868277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_6868277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868277 prefixEnd_6868277 := by exact prefixLift 6868277
  have htrace : WordTrace (prefixWord ++ tailWord_6868277) baseStart_6868277 baseEnd_6868277 := by
    simpa [prefixWord, tailWord_6868277, baseEnd_6868277] using wordTrace_append hprefix tailTrace_6868277
  have hstable : (prefixWord ++ tailWord_6868277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868277).length < 2 ^ (prefixWord ++ tailWord_6868277).sum := by decide
  have hdescent : baseEnd_6868277 < baseStart_6868277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868281 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 1, 4]
def baseStart_6868281 : Nat := 118140960795 + 6868281 * 2 ^ 59
def prefixEnd_6868281 : Nat := 4983230072969 + 3 ^ 40 * 6868281 * 2
def baseEnd_6868281 : Nat := 1175576474381049184233619

theorem tailTrace_6868281 : CollatzResearch.WordTrace tailWord_6868281 prefixEnd_6868281 1175576474381049184233619 := by
  unfold tailWord_6868281
  simp only [CollatzResearch.WordTrace]
  refine ⟨250506788030398420851892697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167004525353598947234595131 250506788030398420851892697)
  ·
    refine ⟨187880091022798815638919523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250506788030398420851892697 187880091022798815638919523)
    ·
      refine ⟨281820136534198223458379285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187880091022798815638919523 281820136534198223458379285)
      ·
        refine ⟨13210318900040541724611529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281820136534198223458379285 13210318900040541724611529)
        ·
          refine ⟨9907739175030406293458647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13210318900040541724611529 9907739175030406293458647)
          ·
            refine ⟨14861608762545609440187971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9907739175030406293458647 14861608762545609440187971)
            ·
              refine ⟨22292413143818414160281957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14861608762545609440187971 22292413143818414160281957)
              ·
                refine ⟨4179827464465952655052867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22292413143818414160281957 4179827464465952655052867)
                ·
                  refine ⟨6269741196698928982579301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179827464465952655052867 6269741196698928982579301)
                  ·
                    refine ⟨1175576474381049184233619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269741196698928982579301 1175576474381049184233619)
                    ·
                      rfl

theorem cell23_6868281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 4].length) (baseStart_6868281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868281 prefixEnd_6868281 := by exact prefixLift 6868281
  have htrace : WordTrace (prefixWord ++ tailWord_6868281) baseStart_6868281 baseEnd_6868281 := by
    simpa [prefixWord, tailWord_6868281, baseEnd_6868281] using wordTrace_append hprefix tailTrace_6868281
  have hstable : (prefixWord ++ tailWord_6868281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868281).length < 2 ^ (prefixWord ++ tailWord_6868281).sum := by decide
  have hdescent : baseEnd_6868281 < baseStart_6868281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868297 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 4, 3, 2]
def baseStart_6868297 : Nat := 118140960795 + 6868297 * 2 ^ 59
def prefixEnd_6868297 : Nat := 4983230072969 + 3 ^ 40 * 6868297 * 2
def baseEnd_6868297 : Nat := 3526737638833619490100783

theorem tailTrace_6868297 : CollatzResearch.WordTrace tailWord_6868297 prefixEnd_6868297 3526737638833619490100783 := by
  unfold tailWord_6868297
  simp only [CollatzResearch.WordTrace]
  refine ⟨250507371598340455584475145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167004914398893637056316763 250507371598340455584475145)
  ·
    refine ⟨187880528698755341688356359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250507371598340455584475145 187880528698755341688356359)
    ·
      refine ⟨281820793048133012532534539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187880528698755341688356359 281820793048133012532534539)
      ·
        refine ⟨422731189572199518798801809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281820793048133012532534539 422731189572199518798801809)
        ·
          refine ⟨317048392179149639099101357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422731189572199518798801809 317048392179149639099101357)
          ·
            refine ⟨118893147067181114662163009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317048392179149639099101357 118893147067181114662163009)
            ·
              refine ⟨89169860300385835996622257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118893147067181114662163009 89169860300385835996622257)
              ·
                refine ⟨66877395225289376997466693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89169860300385835996622257 66877395225289376997466693)
                ·
                  refine ⟨12539511604741758187025005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66877395225289376997466693 12539511604741758187025005)
                  ·
                    refine ⟨4702316851778159320134377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12539511604741758187025005 4702316851778159320134377)
                    ·
                      refine ⟨3526737638833619490100783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702316851778159320134377 3526737638833619490100783)
                      ·
                        rfl

theorem cell23_6868297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3, 2].length) (baseStart_6868297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868297 prefixEnd_6868297 := by exact prefixLift 6868297
  have htrace : WordTrace (prefixWord ++ tailWord_6868297) baseStart_6868297 baseEnd_6868297 := by
    simpa [prefixWord, tailWord_6868297, baseEnd_6868297] using wordTrace_append hprefix tailTrace_6868297
  have hstable : (prefixWord ++ tailWord_6868297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868297).length < 2 ^ (prefixWord ++ tailWord_6868297).sum := by decide
  have hdescent : baseEnd_6868297 < baseStart_6868297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868314 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_6868314 : Nat := 118140960795 + 6868314 * 2 ^ 59
def prefixEnd_6868314 : Nat := 4983230072969 + 3 ^ 40 * 6868314 * 2
def baseEnd_6868314 : Nat := 3526746368004745923588205

theorem tailTrace_6868314 : CollatzResearch.WordTrace tailWord_6868314 prefixEnd_6868314 3526746368004745923588205 := by
  unfold tailWord_6868314
  simp only [CollatzResearch.WordTrace]
  refine ⟨62626997909819716871960999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167005327759519244991895997 62626997909819716871960999)
  ·
    refine ⟨93940496864729575307941499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62626997909819716871960999 93940496864729575307941499)
    ·
      refine ⟨140910745297094362961912249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93940496864729575307941499 140910745297094362961912249)
      ·
        refine ⟨105683058972820772221434187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140910745297094362961912249 105683058972820772221434187)
        ·
          refine ⟨158524588459231158332151281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105683058972820772221434187 158524588459231158332151281)
          ·
            refine ⟨118893441344423368749113461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158524588459231158332151281 118893441344423368749113461)
            ·
              refine ⟨11146260126039690820229387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118893441344423368749113461 11146260126039690820229387)
              ·
                refine ⟨16719390189059536230344081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146260126039690820229387 16719390189059536230344081)
                ·
                  refine ⟨12539542641794652172758061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16719390189059536230344081 12539542641794652172758061)
                  ·
                    refine ⟨4702328490672994564784273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12539542641794652172758061 4702328490672994564784273)
                    ·
                      refine ⟨3526746368004745923588205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702328490672994564784273 3526746368004745923588205)
                      ·
                        rfl

theorem cell23_6868314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_6868314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868314 prefixEnd_6868314 := by exact prefixLift 6868314
  have htrace : WordTrace (prefixWord ++ tailWord_6868314) baseStart_6868314 baseEnd_6868314 := by
    simpa [prefixWord, tailWord_6868314, baseEnd_6868314] using wordTrace_append hprefix tailTrace_6868314
  have hstable : (prefixWord ++ tailWord_6868314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868314).length < 2 ^ (prefixWord ++ tailWord_6868314).sum := by decide
  have hdescent : baseEnd_6868314 < baseStart_6868314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868324 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_6868324 : Nat := 118140960795 + 6868324 * 2 ^ 59
def prefixEnd_6868324 : Nat := 4983230072969 + 3 ^ 40 * 6868324 * 2
def baseEnd_6868324 : Nat := 1175583834270430294821053

theorem tailTrace_6868324 : CollatzResearch.WordTrace tailWord_6868324 prefixEnd_6868324 1175583834270430294821053 := by
  unfold tailWord_6868324
  simp only [CollatzResearch.WordTrace]
  refine ⟨125254178184621319597854013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167005570912828426130472017 125254178184621319597854013)
  ·
    refine ⟨46970316819232994849195255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125254178184621319597854013 46970316819232994849195255)
    ·
      refine ⟨70455475228849492273792883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46970316819232994849195255 70455475228849492273792883)
      ·
        refine ⟨105683212843274238410689325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70455475228849492273792883 105683212843274238410689325)
        ·
          refine ⟨39631204816227839404008497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105683212843274238410689325 39631204816227839404008497)
          ·
            refine ⟨29723403612170879553006373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39631204816227839404008497 29723403612170879553006373)
            ·
              refine ⟨5573138177282039916188695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29723403612170879553006373 5573138177282039916188695)
              ·
                refine ⟨8359707265923059874283043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573138177282039916188695 8359707265923059874283043)
                ·
                  refine ⟨12539560898884589811424565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359707265923059874283043 12539560898884589811424565)
                  ·
                    refine ⟨1175583834270430294821053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12539560898884589811424565 1175583834270430294821053)
                    ·
                      rfl

theorem cell23_6868324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_6868324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868324 prefixEnd_6868324 := by exact prefixLift 6868324
  have htrace : WordTrace (prefixWord ++ tailWord_6868324) baseStart_6868324 baseEnd_6868324 := by
    simpa [prefixWord, tailWord_6868324, baseEnd_6868324] using wordTrace_append hprefix tailTrace_6868324
  have hstable : (prefixWord ++ tailWord_6868324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868324).length < 2 ^ (prefixWord ++ tailWord_6868324).sum := by decide
  have hdescent : baseEnd_6868324 < baseStart_6868324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868357 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_6868357 : Nat := 118140960795 + 6868357 * 2 ^ 59
def prefixEnd_6868357 : Nat := 4983230072969 + 3 ^ 40 * 6868357 * 2
def baseEnd_6868357 : Nat := 3526768447672889255350507

theorem tailTrace_6868357 : CollatzResearch.WordTrace tailWord_6868357 prefixEnd_6868357 3526768447672889255350507 := by
  unfold tailWord_6868357
  simp only [CollatzResearch.WordTrace]
  refine ⟨250509559978123085831659325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167006373318748723887772883 250509559978123085831659325)
  ·
    refine ⟨93941084991796157186872247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250509559978123085831659325 93941084991796157186872247)
    ·
      refine ⟨140911627487694235780308371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93941084991796157186872247 140911627487694235780308371)
      ·
        refine ⟨211367441231541353670462557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140911627487694235780308371 211367441231541353670462557)
        ·
          refine ⟨79262790461828007626423459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211367441231541353670462557 79262790461828007626423459)
          ·
            refine ⟨118894185692742011439635189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79262790461828007626423459 118894185692742011439635189)
            ·
              refine ⟨11146329908694563572465799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118894185692742011439635189 11146329908694563572465799)
              ·
                refine ⟨16719494863041845358698699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146329908694563572465799 16719494863041845358698699)
                ·
                  refine ⟨25079242294562768038048049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16719494863041845358698699 25079242294562768038048049)
                  ·
                    refine ⟨18809431720922076028536037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25079242294562768038048049 18809431720922076028536037)
                    ·
                      refine ⟨3526768447672889255350507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18809431720922076028536037 3526768447672889255350507)
                      ·
                        rfl

theorem cell23_6868357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_6868357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868357 prefixEnd_6868357 := by exact prefixLift 6868357
  have htrace : WordTrace (prefixWord ++ tailWord_6868357) baseStart_6868357 baseEnd_6868357 := by
    simpa [prefixWord, tailWord_6868357, baseEnd_6868357] using wordTrace_append hprefix tailTrace_6868357
  have hstable : (prefixWord ++ tailWord_6868357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868357).length < 2 ^ (prefixWord ++ tailWord_6868357).sum := by decide
  have hdescent : baseEnd_6868357 < baseStart_6868357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868364 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_6868364 : Nat := 118140960795 + 6868364 * 2 ^ 59
def prefixEnd_6868364 : Nat := 4983230072969 + 3 ^ 40 * 6868364 * 2
def baseEnd_6868364 : Nat := 3526772042037470727962975

theorem tailTrace_6868364 : CollatzResearch.WordTrace tailWord_6868364 prefixEnd_6868364 3526772042037470727962975 := by
  unfold tailWord_6868364
  simp only [CollatzResearch.WordTrace]
  refine ⟨125254907644548863013582073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167006543526065150684776097 125254907644548863013582073)
  ·
    refine ⟨93941180733411647260186555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125254907644548863013582073 93941180733411647260186555)
    ·
      refine ⟨140911771100117470890279833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93941180733411647260186555 140911771100117470890279833)
      ·
        refine ⟨105683828325088103167709875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140911771100117470890279833 105683828325088103167709875)
        ·
          refine ⟨158525742487632154751564813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105683828325088103167709875 158525742487632154751564813)
          ·
            refine ⟨59447153432862058031836805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158525742487632154751564813 59447153432862058031836805)
            ·
              refine ⟨11146341268661635880969401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59447153432862058031836805 11146341268661635880969401)
              ·
                refine ⟨8359755951496226910727051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11146341268661635880969401 8359755951496226910727051)
                ·
                  refine ⟨12539633927244340366090577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359755951496226910727051 12539633927244340366090577)
                  ·
                    refine ⟨9404725445433255274567933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12539633927244340366090577 9404725445433255274567933)
                    ·
                      refine ⟨3526772042037470727962975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9404725445433255274567933 3526772042037470727962975)
                      ·
                        rfl

theorem cell23_6868364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_6868364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868364 prefixEnd_6868364 := by exact prefixLift 6868364
  have htrace : WordTrace (prefixWord ++ tailWord_6868364) baseStart_6868364 baseEnd_6868364 := by
    simpa [prefixWord, tailWord_6868364, baseEnd_6868364] using wordTrace_append hprefix tailTrace_6868364
  have hstable : (prefixWord ++ tailWord_6868364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868364).length < 2 ^ (prefixWord ++ tailWord_6868364).sum := by decide
  have hdescent : baseEnd_6868364 < baseStart_6868364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868437 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6868437 : Nat := 118140960795 + 6868437 * 2 ^ 59
def prefixEnd_6868437 : Nat := 4983230072969 + 3 ^ 40 * 6868437 * 2
def baseEnd_6868437 : Nat := 3526809526125248942350139

theorem tailTrace_6868437 : CollatzResearch.WordTrace tailWord_6868437 prefixEnd_6868437 3526809526125248942350139 := by
  unfold tailWord_6868437
  simp only [CollatzResearch.WordTrace]
  refine ⟨250512477817833259494571565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167008318545222172996381043 250512477817833259494571565)
  ·
    refine ⟨93942179181687472310464337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250512477817833259494571565 93942179181687472310464337)
    ·
      refine ⟨70456634386265604232848253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93942179181687472310464337 70456634386265604232848253)
      ·
        refine ⟨26421237894849601587318095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70456634386265604232848253 26421237894849601587318095)
        ·
          refine ⟨39631856842274402380977143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26421237894849601587318095 39631856842274402380977143)
          ·
            refine ⟨59447785263411603571465715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39631856842274402380977143 59447785263411603571465715)
            ·
              refine ⟨89171677895117405357198573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59447785263411603571465715 89171677895117405357198573)
              ·
                refine ⟨33439379210669027008949465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89171677895117405357198573 33439379210669027008949465)
                ·
                  refine ⟨25079534408001770256712099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33439379210669027008949465 25079534408001770256712099)
                  ·
                    refine ⟨37619301612002655385068149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25079534408001770256712099 37619301612002655385068149)
                    ·
                      refine ⟨3526809526125248942350139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37619301612002655385068149 3526809526125248942350139)
                      ·
                        rfl

theorem cell23_6868437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6868437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868437 prefixEnd_6868437 := by exact prefixLift 6868437
  have htrace : WordTrace (prefixWord ++ tailWord_6868437) baseStart_6868437 baseEnd_6868437 := by
    simpa [prefixWord, tailWord_6868437, baseEnd_6868437] using wordTrace_append hprefix tailTrace_6868437
  have hstable : (prefixWord ++ tailWord_6868437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868437).length < 2 ^ (prefixWord ++ tailWord_6868437).sum := by decide
  have hdescent : baseEnd_6868437 < baseStart_6868437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868447 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_6868447 : Nat := 118140960795 + 6868447 * 2 ^ 59
def prefixEnd_6868447 : Nat := 4983230072969 + 3 ^ 40 * 6868447 * 2
def baseEnd_6868447 : Nat := 3526814660931793903225093

theorem tailTrace_6868447 : CollatzResearch.WordTrace tailWord_6868447 prefixEnd_6868447 3526814660931793903225093 := by
  unfold tailWord_6868447
  simp only [CollatzResearch.WordTrace]
  refine ⟨250512842547797031202435595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167008561698531354134957063 250512842547797031202435595)
  ·
    refine ⟨375769263821695546803653393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250512842547797031202435595 375769263821695546803653393)
    ·
      refine ⟨281826947866271660102740045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375769263821695546803653393 281826947866271660102740045)
      ·
        refine ⟨105685105449851872538527517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281826947866271660102740045 105685105449851872538527517)
        ·
          refine ⟨39631914543694452201947819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105685105449851872538527517 39631914543694452201947819)
          ·
            refine ⟨59447871815541678302921729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39631914543694452201947819 59447871815541678302921729)
            ·
              refine ⟨44585903861656258727191297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59447871815541678302921729 44585903861656258727191297)
              ·
                refine ⟨33439427896242194045393473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44585903861656258727191297 33439427896242194045393473)
                ·
                  refine ⟨25079570922181645534045105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33439427896242194045393473 25079570922181645534045105)
                  ·
                    refine ⟨18809678191636234150533829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25079570922181645534045105 18809678191636234150533829)
                    ·
                      refine ⟨3526814660931793903225093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18809678191636234150533829 3526814660931793903225093)
                      ·
                        rfl

theorem cell23_6868447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_6868447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868447 prefixEnd_6868447 := by exact prefixLift 6868447
  have htrace : WordTrace (prefixWord ++ tailWord_6868447) baseStart_6868447 baseEnd_6868447 := by
    simpa [prefixWord, tailWord_6868447, baseEnd_6868447] using wordTrace_append hprefix tailTrace_6868447
  have hstable : (prefixWord ++ tailWord_6868447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868447).length < 2 ^ (prefixWord ++ tailWord_6868447).sum := by decide
  have hdescent : baseEnd_6868447 < baseStart_6868447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868491 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 5]
def baseStart_6868491 : Nat := 118140960795 + 6868491 * 2 ^ 59
def prefixEnd_6868491 : Nat := 4983230072969 + 3 ^ 40 * 6868491 * 2
def baseEnd_6868491 : Nat := 391870806008954636786099

theorem tailTrace_6868491 : CollatzResearch.WordTrace tailWord_6868491 prefixEnd_6868491 391870806008954636786099 := by
  unfold tailWord_6868491
  simp only [CollatzResearch.WordTrace]
  refine ⟨250514447359637626717037327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167009631573091751144691551 250514447359637626717037327)
  ·
    refine ⟨375771671039456440075555991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250514447359637626717037327 375771671039456440075555991)
    ·
      refine ⟨563657506559184660113333987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375771671039456440075555991 563657506559184660113333987)
      ·
        refine ⟨845486259838776990170000981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563657506559184660113333987 845486259838776990170000981)
        ·
          refine ⟨9908042107485667853554699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 845486259838776990170000981 9908042107485667853554699)
          ·
            refine ⟨14862063161228501780332049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9908042107485667853554699 14862063161228501780332049)
            ·
              refine ⟨11146547370921376335249037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14862063161228501780332049 11146547370921376335249037)
              ·
                refine ⟨4179955264095516125718389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11146547370921376335249037 4179955264095516125718389)
                ·
                  refine ⟨391870806008954636786099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4179955264095516125718389 391870806008954636786099)
                  ·
                    rfl

theorem cell23_6868491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 5].length) (baseStart_6868491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868491 prefixEnd_6868491 := by exact prefixLift 6868491
  have htrace : WordTrace (prefixWord ++ tailWord_6868491) baseStart_6868491 baseEnd_6868491 := by
    simpa [prefixWord, tailWord_6868491, baseEnd_6868491] using wordTrace_append hprefix tailTrace_6868491
  have hstable : (prefixWord ++ tailWord_6868491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868491).length < 2 ^ (prefixWord ++ tailWord_6868491).sum := by decide
  have hdescent : baseEnd_6868491 < baseStart_6868491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868544 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_6868544 : Nat := 118140960795 + 6868544 * 2 ^ 59
def prefixEnd_6868544 : Nat := 4983230072969 + 3 ^ 40 * 6868544 * 2
def baseEnd_6868544 : Nat := 3526864468555280023712147

theorem tailTrace_6868544 : CollatzResearch.WordTrace tailWord_6868544 prefixEnd_6868544 3526864468555280023712147 := by
  unfold tailWord_6868544
  simp only [CollatzResearch.WordTrace]
  refine ⟨125258190214222808384358343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167010920285630411179144457 125258190214222808384358343)
  ·
    refine ⟨187887285321334212576537515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125258190214222808384358343 187887285321334212576537515)
    ·
      refine ⟨281830927982001318864806273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187887285321334212576537515 281830927982001318864806273)
      ·
        refine ⟨211373195986500989148604705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281830927982001318864806273 211373195986500989148604705)
        ·
          refine ⟨158529896989875741861453529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211373195986500989148604705 158529896989875741861453529)
          ·
            refine ⟨118897422742406806396090147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158529896989875741861453529 118897422742406806396090147)
            ·
              refine ⟨178346134113610209594135221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118897422742406806396090147 178346134113610209594135221)
              ·
                refine ⟨16719950073150957149450177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178346134113610209594135221 16719950073150957149450177)
                ·
                  refine ⟨12539962554863217862087633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16719950073150957149450177 12539962554863217862087633)
                  ·
                    refine ⟨9404971916147413396565725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12539962554863217862087633 9404971916147413396565725)
                    ·
                      refine ⟨3526864468555280023712147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9404971916147413396565725 3526864468555280023712147)
                      ·
                        rfl

theorem cell23_6868544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_6868544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868544 prefixEnd_6868544 := by exact prefixLift 6868544
  have htrace : WordTrace (prefixWord ++ tailWord_6868544) baseStart_6868544 baseEnd_6868544 := by
    simpa [prefixWord, tailWord_6868544, baseEnd_6868544] using wordTrace_append hprefix tailTrace_6868544
  have hstable : (prefixWord ++ tailWord_6868544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868544).length < 2 ^ (prefixWord ++ tailWord_6868544).sum := by decide
  have hdescent : baseEnd_6868544 < baseStart_6868544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868564 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 6]
def baseStart_6868564 : Nat := 118140960795 + 6868564 * 2 ^ 59
def prefixEnd_6868564 : Nat := 4983230072969 + 3 ^ 40 * 6868564 * 2
def baseEnd_6868564 : Nat := 391874970907596660606895

theorem tailTrace_6868564 : CollatzResearch.WordTrace tailWord_6868564 prefixEnd_6868564 391874970907596660606895 := by
  unfold tailWord_6868564
  simp only [CollatzResearch.WordTrace]
  refine ⟨125258554944186580092222373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167011406592248773456296497 125258554944186580092222373)
  ·
    refine ⟨23485979052034983767291695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125258554944186580092222373 23485979052034983767291695)
    ·
      refine ⟨35228968578052475650937543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485979052034983767291695 35228968578052475650937543)
      ·
        refine ⟨52843452867078713476406315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35228968578052475650937543 52843452867078713476406315)
        ·
          refine ⟨79265179300618070214609473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52843452867078713476406315 79265179300618070214609473)
          ·
            refine ⟨59448884475463552660957105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79265179300618070214609473 59448884475463552660957105)
            ·
              refine ⟨44586663356597664495717829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59448884475463552660957105 44586663356597664495717829)
              ·
                refine ⟨8359999379362062092947093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44586663356597664495717829 8359999379362062092947093)
                ·
                  refine ⟨391874970907596660606895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8359999379362062092947093 391874970907596660606895)
                  ·
                    rfl

theorem cell23_6868564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_6868564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868564 prefixEnd_6868564 := by exact prefixLift 6868564
  have htrace : WordTrace (prefixWord ++ tailWord_6868564) baseStart_6868564 baseEnd_6868564 := by
    simpa [prefixWord, tailWord_6868564, baseEnd_6868564] using wordTrace_append hprefix tailTrace_6868564
  have hstable : (prefixWord ++ tailWord_6868564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868564).length < 2 ^ (prefixWord ++ tailWord_6868564).sum := by decide
  have hdescent : baseEnd_6868564 < baseStart_6868564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868581 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 6]
def baseStart_6868581 : Nat := 118140960795 + 6868581 * 2 ^ 59
def prefixEnd_6868581 : Nat := 4983230072969 + 3 ^ 40 * 6868581 * 2
def baseEnd_6868581 : Nat := 391875940815499597661053

theorem tailTrace_6868581 : CollatzResearch.WordTrace tailWord_6868581 prefixEnd_6868581 391875940815499597661053 := by
  unfold tailWord_6868581
  simp only [CollatzResearch.WordTrace]
  refine ⟨250517729929311572087813597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167011819952874381391875731 250517729929311572087813597)
  ·
    refine ⟨93944148723491839532930099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250517729929311572087813597 93944148723491839532930099)
    ·
      refine ⟨140916223085237759299395149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93944148723491839532930099 140916223085237759299395149)
      ·
        refine ⟨52843583656964159737273181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140916223085237759299395149 52843583656964159737273181)
        ·
          refine ⟨19816343871361559901477443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52843583656964159737273181 19816343871361559901477443)
          ·
            refine ⟨29724515807042339852216165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19816343871361559901477443 29724515807042339852216165)
            ·
              refine ⟨5573346713820438722290531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29724515807042339852216165 5573346713820438722290531)
              ·
                refine ⟨8360020070730658083435797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573346713820438722290531 8360020070730658083435797)
                ·
                  refine ⟨391875940815499597661053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8360020070730658083435797 391875940815499597661053)
                  ·
                    rfl

theorem cell23_6868581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_6868581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868581 prefixEnd_6868581 := by exact prefixLift 6868581
  have htrace : WordTrace (prefixWord ++ tailWord_6868581) baseStart_6868581 baseEnd_6868581 := by
    simpa [prefixWord, tailWord_6868581, baseEnd_6868581] using wordTrace_append hprefix tailTrace_6868581
  have hstable : (prefixWord ++ tailWord_6868581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868581).length < 2 ^ (prefixWord ++ tailWord_6868581).sum := by decide
  have hdescent : baseEnd_6868581 < baseStart_6868581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868608 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 1, 1, 3]
def baseStart_6868608 : Nat := 118140960795 + 6868608 * 2 ^ 59
def prefixEnd_6868608 : Nat := 4983230072969 + 3 ^ 40 * 6868608 * 2
def baseEnd_6868608 : Nat := 3526897331317167773311853

theorem tailTrace_6868608 : CollatzResearch.WordTrace tailWord_6868608 prefixEnd_6868608 3526897331317167773311853 := by
  unfold tailWord_6868608
  simp only [CollatzResearch.WordTrace]
  refine ⟨125259357350106877849523239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167012476466809170466030985 125259357350106877849523239)
  ·
    refine ⟨187889036025160316774284859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125259357350106877849523239 187889036025160316774284859)
    ·
      refine ⟨281833554037740475161427289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187889036025160316774284859 281833554037740475161427289)
      ·
        refine ⟨211375165528305356371070467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281833554037740475161427289 211375165528305356371070467)
        ·
          refine ⟨317062748292458034556605701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211375165528305356371070467 317062748292458034556605701)
          ·
            refine ⟨59449265304835881479363569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317062748292458034556605701 59449265304835881479363569)
            ·
              refine ⟨44586948978626911109522677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59449265304835881479363569 44586948978626911109522677)
              ·
                refine ⟨4180026466746272916517751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44586948978626911109522677 4180026466746272916517751)
                ·
                  refine ⟨6270039700119409374776627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180026466746272916517751 6270039700119409374776627)
                  ·
                    refine ⟨9405059550179114062164941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270039700119409374776627 9405059550179114062164941)
                    ·
                      refine ⟨3526897331317167773311853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405059550179114062164941 3526897331317167773311853)
                      ·
                        rfl

theorem cell23_6868608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_6868608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868608 prefixEnd_6868608 := by exact prefixLift 6868608
  have htrace : WordTrace (prefixWord ++ tailWord_6868608) baseStart_6868608 baseEnd_6868608 := by
    simpa [prefixWord, tailWord_6868608, baseEnd_6868608] using wordTrace_append hprefix tailTrace_6868608
  have hstable : (prefixWord ++ tailWord_6868608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868608).length < 2 ^ (prefixWord ++ tailWord_6868608).sum := by decide
  have hdescent : baseEnd_6868608 < baseStart_6868608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868618 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_6868618 : Nat := 118140960795 + 6868618 * 2 ^ 59
def prefixEnd_6868618 : Nat := 4983230072969 + 3 ^ 40 * 6868618 * 2
def baseEnd_6868618 : Nat := 3526902466123712734186807

theorem tailTrace_6868618 : CollatzResearch.WordTrace tailWord_6868618 prefixEnd_6868618 3526902466123712734186807 := by
  unfold tailWord_6868618
  simp only [CollatzResearch.WordTrace]
  refine ⟨62629769857544381851727627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167012719620118351604607005 62629769857544381851727627)
  ·
    refine ⟨93944654786316572777591441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62629769857544381851727627 93944654786316572777591441)
    ·
      refine ⟨70458491089737429583193581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93944654786316572777591441 70458491089737429583193581)
      ·
        refine ⟨26421934158651536093697593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70458491089737429583193581 26421934158651536093697593)
        ·
          refine ⟨19816450618988652070273195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26421934158651536093697593 19816450618988652070273195)
          ·
            refine ⟨29724675928482978105409793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19816450618988652070273195 29724675928482978105409793)
            ·
              refine ⟨22293506946362233579057345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29724675928482978105409793 22293506946362233579057345)
              ·
                refine ⟨16720130209771675184293009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22293506946362233579057345 16720130209771675184293009)
                ·
                  refine ⟨12540097657328756388219757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16720130209771675184293009 12540097657328756388219757)
                  ·
                    refine ⟨4702536621498283645582409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12540097657328756388219757 4702536621498283645582409)
                    ·
                      refine ⟨3526902466123712734186807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702536621498283645582409 3526902466123712734186807)
                      ·
                        rfl

theorem cell23_6868618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_6868618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868618 prefixEnd_6868618 := by exact prefixLift 6868618
  have htrace : WordTrace (prefixWord ++ tailWord_6868618) baseStart_6868618 baseEnd_6868618 := by
    simpa [prefixWord, tailWord_6868618, baseEnd_6868618] using wordTrace_append hprefix tailTrace_6868618
  have hstable : (prefixWord ++ tailWord_6868618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868618).length < 2 ^ (prefixWord ++ tailWord_6868618).sum := by decide
  have hdescent : baseEnd_6868618 < baseStart_6868618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868624 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_6868624 : Nat := 118140960795 + 6868624 * 2 ^ 59
def prefixEnd_6868624 : Nat := 4983230072969 + 3 ^ 40 * 6868624 * 2
def baseEnd_6868624 : Nat := 1175635182335879903570593

theorem tailTrace_6868624 : CollatzResearch.WordTrace tailWord_6868624 prefixEnd_6868624 1175635182335879903570593 := by
  unfold tailWord_6868624
  simp only [CollatzResearch.WordTrace]
  refine ⟨125259649134077895215814463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167012865512103860287752617 125259649134077895215814463)
  ·
    refine ⟨187889473701116842823721695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125259649134077895215814463 187889473701116842823721695)
    ·
      refine ⟨281834210551675264235582543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187889473701116842823721695 281834210551675264235582543)
      ·
        refine ⟨422751315827512896353373815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281834210551675264235582543 422751315827512896353373815)
        ·
          refine ⟨634126973741269344530060723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422751315827512896353373815 634126973741269344530060723)
          ·
            refine ⟨951190460611904016795091085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634126973741269344530060723 951190460611904016795091085)
            ·
              refine ⟨356696422729464006298159157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 951190460611904016795091085 356696422729464006298159157)
              ·
                refine ⟨33440289630887250590452421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356696422729464006298159157 33440289630887250590452421)
                ·
                  refine ⟨6270054305791359485709829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33440289630887250590452421 6270054305791359485709829)
                  ·
                    refine ⟨1175635182335879903570593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6270054305791359485709829 1175635182335879903570593)
                    ·
                      rfl

theorem cell23_6868624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_6868624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868624 prefixEnd_6868624 := by exact prefixLift 6868624
  have htrace : WordTrace (prefixWord ++ tailWord_6868624) baseStart_6868624 baseEnd_6868624 := by
    simpa [prefixWord, tailWord_6868624, baseEnd_6868624] using wordTrace_append hprefix tailTrace_6868624
  have hstable : (prefixWord ++ tailWord_6868624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868624).length < 2 ^ (prefixWord ++ tailWord_6868624).sum := by decide
  have hdescent : baseEnd_6868624 < baseStart_6868624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868641 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_6868641 : Nat := 118140960795 + 6868641 * 2 ^ 59
def prefixEnd_6868641 : Nat := 4983230072969 + 3 ^ 40 * 6868641 * 2
def baseEnd_6868641 : Nat := 1175638092059588714733067

theorem tailTrace_6868641 : CollatzResearch.WordTrace tailWord_6868641 prefixEnd_6868641 1175638092059588714733067 := by
  unfold tailWord_6868641
  simp only [CollatzResearch.WordTrace]
  refine ⟨250519918309094202334997777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167013278872729468223331851 250519918309094202334997777)
  ·
    refine ⟨187889938731820651751248333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250519918309094202334997777 187889938731820651751248333)
    ·
      refine ⟨70458727024432744406718125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187889938731820651751248333 70458727024432744406718125)
      ·
        refine ⟨26422022634162279152519297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70458727024432744406718125 26422022634162279152519297)
        ·
          refine ⟨19816516975621709364389473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26422022634162279152519297 19816516975621709364389473)
          ·
            refine ⟨14862387731716282023292105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19816516975621709364389473 14862387731716282023292105)
            ·
              refine ⟨11146790798787211517469079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14862387731716282023292105 11146790798787211517469079)
              ·
                refine ⟨16720186198180817276203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146790798787211517469079 16720186198180817276203619)
                ·
                  refine ⟨25080279297271225914305429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16720186198180817276203619 25080279297271225914305429)
                  ·
                    refine ⟨1175638092059588714733067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25080279297271225914305429 1175638092059588714733067)
                    ·
                      rfl

theorem cell23_6868641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_6868641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868641 prefixEnd_6868641 := by exact prefixLift 6868641
  have htrace : WordTrace (prefixWord ++ tailWord_6868641) baseStart_6868641 baseEnd_6868641 := by
    simpa [prefixWord, tailWord_6868641, baseEnd_6868641] using wordTrace_append hprefix tailTrace_6868641
  have hstable : (prefixWord ++ tailWord_6868641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868641).length < 2 ^ (prefixWord ++ tailWord_6868641).sum := by decide
  have hdescent : baseEnd_6868641 < baseStart_6868641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868662 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6868662 : Nat := 118140960795 + 6868662 * 2 ^ 59
def prefixEnd_6868662 : Nat := 4983230072969 + 3 ^ 40 * 6868662 * 2
def baseEnd_6868662 : Nat := 1175641686424170187345535

theorem tailTrace_6868662 : CollatzResearch.WordTrace tailWord_6868662 prefixEnd_6868662 1175641686424170187345535 := by
  unfold tailWord_6868662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657542765126132682594515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167013789494678748614341493 15657542765126132682594515)
  ·
    refine ⟨23486314147689199023891773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15657542765126132682594515 23486314147689199023891773)
    ·
      refine ⟨8807367805383449633959415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23486314147689199023891773 8807367805383449633959415)
      ·
        refine ⟨13211051708075174450939123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807367805383449633959415 13211051708075174450939123)
        ·
          refine ⟨19816577562112761676408685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13211051708075174450939123 19816577562112761676408685)
          ·
            refine ⟨7431216585792285628653257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19816577562112761676408685 7431216585792285628653257)
            ·
              refine ⟨5573412439344214221489943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7431216585792285628653257 5573412439344214221489943)
              ·
                refine ⟨8360118659016321332234915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573412439344214221489943 8360118659016321332234915)
                ·
                  refine ⟨12540177988524481998352373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8360118659016321332234915 12540177988524481998352373)
                  ·
                    refine ⟨1175641686424170187345535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12540177988524481998352373 1175641686424170187345535)
                    ·
                      rfl

theorem cell23_6868662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6868662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868662 prefixEnd_6868662 := by exact prefixLift 6868662
  have htrace : WordTrace (prefixWord ++ tailWord_6868662) baseStart_6868662 baseEnd_6868662 := by
    simpa [prefixWord, tailWord_6868662, baseEnd_6868662] using wordTrace_append hprefix tailTrace_6868662
  have hstable : (prefixWord ++ tailWord_6868662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868662).length < 2 ^ (prefixWord ++ tailWord_6868662).sum := by decide
  have hdescent : baseEnd_6868662 < baseStart_6868662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868665 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6868665 : Nat := 118140960795 + 6868665 * 2 ^ 59
def prefixEnd_6868665 : Nat := 4983230072969 + 3 ^ 40 * 6868665 * 2
def baseEnd_6868665 : Nat := 3526926599714474050299091

theorem tailTrace_6868665 : CollatzResearch.WordTrace tailWord_6868665 prefixEnd_6868665 3526926599714474050299091 := by
  unfold tailWord_6868665
  simp only [CollatzResearch.WordTrace]
  refine ⟨250520793661007254433871449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167013862440671502955914299 250520793661007254433871449)
  ·
    refine ⟨187890595245755440825403587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250520793661007254433871449 187890595245755440825403587)
    ·
      refine ⟨281835892868633161238105381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187890595245755440825403587 281835892868633161238105381)
      ·
        refine ⟨52844229912868717732144759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281835892868633161238105381 52844229912868717732144759)
        ·
          refine ⟨79266344869303076598217139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52844229912868717732144759 79266344869303076598217139)
          ·
            refine ⟨118899517303954614897325709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79266344869303076598217139 118899517303954614897325709)
            ·
              refine ⟨44587318988982980586497141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118899517303954614897325709 44587318988982980586497141)
              ·
                refine ⟨4180061155217154429984107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44587318988982980586497141 4180061155217154429984107)
                ·
                  refine ⟨6270091732825731644976161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180061155217154429984107 6270091732825731644976161)
                  ·
                    refine ⟨4702568799619298733732121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6270091732825731644976161 4702568799619298733732121)
                    ·
                      refine ⟨3526926599714474050299091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702568799619298733732121 3526926599714474050299091)
                      ·
                        rfl

theorem cell23_6868665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6868665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868665 prefixEnd_6868665 := by exact prefixLift 6868665
  have htrace : WordTrace (prefixWord ++ tailWord_6868665) baseStart_6868665 baseEnd_6868665 := by
    simpa [prefixWord, tailWord_6868665, baseEnd_6868665] using wordTrace_append hprefix tailTrace_6868665
  have hstable : (prefixWord ++ tailWord_6868665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868665).length < 2 ^ (prefixWord ++ tailWord_6868665).sum := by decide
  have hdescent : baseEnd_6868665 < baseStart_6868665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868668 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6868668 : Nat := 118140960795 + 6868668 * 2 ^ 59
def prefixEnd_6868668 : Nat := 4983230072969 + 3 ^ 40 * 6868668 * 2
def baseEnd_6868668 : Nat := 3526928140156437538561577

theorem tailTrace_6868668 : CollatzResearch.WordTrace tailWord_6868668 prefixEnd_6868668 3526928140156437538561577 := by
  unfold tailWord_6868668
  simp only [CollatzResearch.WordTrace]
  refine ⟨125260451539998192973115329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167013935386664257297487105 125260451539998192973115329)
  ·
    refine ⟨93945338654998644729836497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125260451539998192973115329 93945338654998644729836497)
    ·
      refine ⟨70459003991248983547377373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93945338654998644729836497 70459003991248983547377373)
      ·
        refine ⟨26422126496718368830266515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70459003991248983547377373 26422126496718368830266515)
        ·
          refine ⟨39633189745077553245399773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26422126496718368830266515 39633189745077553245399773)
          ·
            refine ⟨14862446154404082467024915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39633189745077553245399773 14862446154404082467024915)
            ·
              refine ⟨22293669231606123700537373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14862446154404082467024915 22293669231606123700537373)
              ·
                refine ⟨8360125961852296387701515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22293669231606123700537373 8360125961852296387701515)
                ·
                  refine ⟨12540188942778444581552273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8360125961852296387701515 12540188942778444581552273)
                  ·
                    refine ⟨9405141707083833436164205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12540188942778444581552273 9405141707083833436164205)
                    ·
                      refine ⟨3526928140156437538561577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405141707083833436164205 3526928140156437538561577)
                      ·
                        rfl

theorem cell23_6868668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6868668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868668 prefixEnd_6868668 := by exact prefixLift 6868668
  have htrace : WordTrace (prefixWord ++ tailWord_6868668) baseStart_6868668 baseEnd_6868668 := by
    simpa [prefixWord, tailWord_6868668, baseEnd_6868668] using wordTrace_append hprefix tailTrace_6868668
  have hstable : (prefixWord ++ tailWord_6868668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868668).length < 2 ^ (prefixWord ++ tailWord_6868668).sum := by decide
  have hdescent : baseEnd_6868668 < baseStart_6868668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868698 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_6868698 : Nat := 118140960795 + 6868698 * 2 ^ 59
def prefixEnd_6868698 : Nat := 4983230072969 + 3 ^ 40 * 6868698 * 2
def baseEnd_6868698 : Nat := 3526943544576072421186439

theorem tailTrace_6868698 : CollatzResearch.WordTrace tailWord_6868698 prefixEnd_6868698 3526943544576072421186439 := by
  unfold tailWord_6868698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630499317471925267455687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167014664846591800713215165 62630499317471925267455687)
  ·
    refine ⟨93945748976207887901183531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62630499317471925267455687 93945748976207887901183531)
    ·
      refine ⟨140918623464311831851775297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93945748976207887901183531 140918623464311831851775297)
      ·
        refine ⟨105688967598233873888831473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140918623464311831851775297 105688967598233873888831473)
        ·
          refine ⟨79266725698675405416623605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105688967598233873888831473 79266725698675405416623605)
          ·
            refine ⟨7431255534250819257808463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79266725698675405416623605 7431255534250819257808463)
            ·
              refine ⟨11146883301376228886712695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431255534250819257808463 11146883301376228886712695)
              ·
                refine ⟨16720324952064343330069043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146883301376228886712695 16720324952064343330069043)
                ·
                  refine ⟨25080487428096514995103565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16720324952064343330069043 25080487428096514995103565)
                  ·
                    refine ⟨9405182785536193123163837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25080487428096514995103565 9405182785536193123163837)
                    ·
                      refine ⟨3526943544576072421186439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405182785536193123163837 3526943544576072421186439)
                      ·
                        rfl

theorem cell23_6868698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_6868698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868698 prefixEnd_6868698 := by exact prefixLift 6868698
  have htrace : WordTrace (prefixWord ++ tailWord_6868698) baseStart_6868698 baseEnd_6868698 := by
    simpa [prefixWord, tailWord_6868698, baseEnd_6868698] using wordTrace_append hprefix tailTrace_6868698
  have hstable : (prefixWord ++ tailWord_6868698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868698).length < 2 ^ (prefixWord ++ tailWord_6868698).sum := by decide
  have hdescent : baseEnd_6868698 < baseStart_6868698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868704 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_6868704 : Nat := 118140960795 + 6868704 * 2 ^ 59
def prefixEnd_6868704 : Nat := 4983230072969 + 3 ^ 40 * 6868704 * 2
def baseEnd_6868704 : Nat := 3526946625459999397711411

theorem tailTrace_6868704 : CollatzResearch.WordTrace tailWord_6868704 prefixEnd_6868704 3526946625459999397711411 := by
  unfold tailWord_6868704
  simp only [CollatzResearch.WordTrace]
  refine ⟨125261108053932982047270583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167014810738577309396360777 125261108053932982047270583)
  ·
    refine ⟨187891662080899473070905875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125261108053932982047270583 187891662080899473070905875)
    ·
      refine ⟨281837493121349209606358813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187891662080899473070905875 281837493121349209606358813)
      ·
        refine ⟨105689059920505953602384555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281837493121349209606358813 105689059920505953602384555)
        ·
          refine ⟨158533589880758930403576833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105689059920505953602384555 158533589880758930403576833)
          ·
            refine ⟨118900192410569197802682625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158533589880758930403576833 118900192410569197802682625)
            ·
              refine ⟨89175144307926898352011969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118900192410569197802682625 89175144307926898352011969)
              ·
                refine ⟨66881358230945173764008977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89175144307926898352011969 66881358230945173764008977)
                ·
                  refine ⟨50161018673208880323006733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66881358230945173764008977 50161018673208880323006733)
                  ·
                    refine ⟨18810382002453330121127525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50161018673208880323006733 18810382002453330121127525)
                    ·
                      refine ⟨3526946625459999397711411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18810382002453330121127525 3526946625459999397711411)
                      ·
                        rfl

theorem cell23_6868704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_6868704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868704 prefixEnd_6868704 := by exact prefixLift 6868704
  have htrace : WordTrace (prefixWord ++ tailWord_6868704) baseStart_6868704 baseEnd_6868704 := by
    simpa [prefixWord, tailWord_6868704, baseEnd_6868704] using wordTrace_append hprefix tailTrace_6868704
  have hstable : (prefixWord ++ tailWord_6868704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868704).length < 2 ^ (prefixWord ++ tailWord_6868704).sum := by decide
  have hdescent : baseEnd_6868704 < baseStart_6868704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868714 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_6868714 : Nat := 118140960795 + 6868714 * 2 ^ 59
def prefixEnd_6868714 : Nat := 4983230072969 + 3 ^ 40 * 6868714 * 2
def baseEnd_6868714 : Nat := 1175650586755514786195455

theorem tailTrace_6868714 : CollatzResearch.WordTrace tailWord_6868714 prefixEnd_6868714 1175650586755514786195455 := by
  unfold tailWord_6868714
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630645209457433950601299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167015053891886490534936797 62630645209457433950601299)
  ·
    refine ⟨93945967814186150925901949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62630645209457433950601299 93945967814186150925901949)
    ·
      refine ⟨35229737930319806597213231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93945967814186150925901949 35229737930319806597213231)
      ·
        refine ⟨52844606895479709895819847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35229737930319806597213231 52844606895479709895819847)
        ·
          refine ⟨79266910343219564843729771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52844606895479709895819847 79266910343219564843729771)
          ·
            refine ⟨118900365514829347265594657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79266910343219564843729771 118900365514829347265594657)
            ·
              refine ⟨89175274136122010449195993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118900365514829347265594657 89175274136122010449195993)
              ·
                refine ⟨66881455602091507836896995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89175274136122010449195993 66881455602091507836896995)
                ·
                  refine ⟨100322183403137261755345493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66881455602091507836896995 100322183403137261755345493)
                  ·
                    refine ⟨1175650586755514786195455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100322183403137261755345493 1175650586755514786195455)
                    ·
                      rfl

theorem cell23_6868714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_6868714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868714 prefixEnd_6868714 := by exact prefixLift 6868714
  have htrace : WordTrace (prefixWord ++ tailWord_6868714) baseStart_6868714 baseEnd_6868714 := by
    simpa [prefixWord, tailWord_6868714, baseEnd_6868714] using wordTrace_append hprefix tailTrace_6868714
  have hstable : (prefixWord ++ tailWord_6868714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868714).length < 2 ^ (prefixWord ++ tailWord_6868714).sum := by decide
  have hdescent : baseEnd_6868714 < baseStart_6868714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868862 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6868862 : Nat := 118140960795 + 6868862 * 2 ^ 59
def prefixEnd_6868862 : Nat := 4983230072969 + 3 ^ 40 * 6868862 * 2
def baseEnd_6868862 : Nat := 3527027755403409779535685

theorem tailTrace_6868862 : CollatzResearch.WordTrace tailWord_6868862 prefixEnd_6868862 3527027755403409779535685 := by
  unfold tailWord_6868862
  simp only [CollatzResearch.WordTrace]
  refine ⟨31315997355161694634849105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167018652560862371385861893 31315997355161694634849105)
  ·
    refine ⟨23486998016371270976136829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31315997355161694634849105 23486998016371270976136829)
    ·
      refine ⟨8807624256139226616051311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23486998016371270976136829 8807624256139226616051311)
      ·
        refine ⟨13211436384208839924076967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807624256139226616051311 13211436384208839924076967)
        ·
          refine ⟨19817154576313259886115451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13211436384208839924076967 19817154576313259886115451)
          ·
            refine ⟨29725731864469889829173177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19817154576313259886115451 29725731864469889829173177)
            ·
              refine ⟨22294298898352417371879883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29725731864469889829173177 22294298898352417371879883)
              ·
                refine ⟨33441448347528626057819825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22294298898352417371879883 33441448347528626057819825)
                ·
                  refine ⟨25081086260646469543364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33441448347528626057819825 25081086260646469543364869)
                  ·
                    refine ⟨4702703673871213039380913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25081086260646469543364869 4702703673871213039380913)
                    ·
                      refine ⟨3527027755403409779535685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702703673871213039380913 3527027755403409779535685)
                      ·
                        rfl

theorem cell23_6868862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6868862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868862 prefixEnd_6868862 := by exact prefixLift 6868862
  have htrace : WordTrace (prefixWord ++ tailWord_6868862) baseStart_6868862 baseEnd_6868862 := by
    simpa [prefixWord, tailWord_6868862, baseEnd_6868862] using wordTrace_append hprefix tailTrace_6868862
  have hstable : (prefixWord ++ tailWord_6868862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868862).length < 2 ^ (prefixWord ++ tailWord_6868862).sum := by decide
  have hdescent : baseEnd_6868862 < baseStart_6868862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868881 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_6868881 : Nat := 118140960795 + 6868881 * 2 ^ 59
def prefixEnd_6868881 : Nat := 4983230072969 + 3 ^ 40 * 6868881 * 2
def baseEnd_6868881 : Nat := 1175679170511948401732699

theorem tailTrace_6868881 : CollatzResearch.WordTrace tailWord_6868881 prefixEnd_6868881 1175679170511948401732699 := by
  unfold tailWord_6868881
  simp only [CollatzResearch.WordTrace]
  refine ⟨250528671828224723323734497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167019114552149815549156331 250528671828224723323734497)
  ·
    refine ⟨187896503871168542492800873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250528671828224723323734497 187896503871168542492800873)
    ·
      refine ⟨140922377903376406869600655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187896503871168542492800873 140922377903376406869600655)
      ·
        refine ⟨211383566855064610304400983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140922377903376406869600655 211383566855064610304400983)
        ·
          refine ⟨317075350282596915456601475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211383566855064610304400983 317075350282596915456601475)
          ·
            refine ⟨475613025423895373184902213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317075350282596915456601475 475613025423895373184902213)
            ·
              refine ⟨89177442266980382472169165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 475613025423895373184902213 89177442266980382472169165)
              ·
                refine ⟨33441540850117643427063437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89177442266980382472169165 33441540850117643427063437)
                ·
                  refine ⟨12540577818794116285148789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33441540850117643427063437 12540577818794116285148789)
                  ·
                    refine ⟨1175679170511948401732699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12540577818794116285148789 1175679170511948401732699)
                    ·
                      rfl

theorem cell23_6868881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_6868881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868881 prefixEnd_6868881 := by exact prefixLift 6868881
  have htrace : WordTrace (prefixWord ++ tailWord_6868881) baseStart_6868881 baseEnd_6868881 := by
    simpa [prefixWord, tailWord_6868881, baseEnd_6868881] using wordTrace_append hprefix tailTrace_6868881
  have hstable : (prefixWord ++ tailWord_6868881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868881).length < 2 ^ (prefixWord ++ tailWord_6868881).sum := by decide
  have hdescent : baseEnd_6868881 < baseStart_6868881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868935 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_6868935 : Nat := 118140960795 + 6868935 * 2 ^ 59
def prefixEnd_6868935 : Nat := 4983230072969 + 3 ^ 40 * 6868935 * 2
def baseEnd_6868935 : Nat := 3527065239491187993922849

theorem tailTrace_6868935 : CollatzResearch.WordTrace tailWord_6868935 prefixEnd_6868935 3527065239491187993922849 := by
  unfold tailWord_6868935
  simp only [CollatzResearch.WordTrace]
  refine ⟨250530641370029090546200259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167020427580019393697466839 250530641370029090546200259)
  ·
    refine ⟨375795962055043635819300389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250530641370029090546200259 375795962055043635819300389)
    ·
      refine ⟨70461742885320681716118823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375795962055043635819300389 70461742885320681716118823)
      ·
        refine ⟨105692614327981022574178235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70461742885320681716118823 105692614327981022574178235)
        ·
          refine ⟨158538921491971533861267353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105692614327981022574178235 158538921491971533861267353)
          ·
            refine ⟨118904191118978650395950515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158538921491971533861267353 118904191118978650395950515)
            ·
              refine ⟨178356286678467975593925773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118904191118978650395950515 178356286678467975593925773)
              ·
                refine ⟨66883607504425490847722165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178356286678467975593925773 66883607504425490847722165)
                ·
                  refine ⟨6270338203539889766973953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66883607504425490847722165 6270338203539889766973953)
                  ·
                    refine ⟨4702753652654917325230465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6270338203539889766973953 4702753652654917325230465)
                    ·
                      refine ⟨3527065239491187993922849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702753652654917325230465 3527065239491187993922849)
                      ·
                        rfl

theorem cell23_6868935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_6868935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868935 prefixEnd_6868935 := by exact prefixLift 6868935
  have htrace : WordTrace (prefixWord ++ tailWord_6868935) baseStart_6868935 baseEnd_6868935 := by
    simpa [prefixWord, tailWord_6868935, baseEnd_6868935] using wordTrace_append hprefix tailTrace_6868935
  have hstable : (prefixWord ++ tailWord_6868935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868935).length < 2 ^ (prefixWord ++ tailWord_6868935).sum := by decide
  have hdescent : baseEnd_6868935 < baseStart_6868935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868968 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6868968 : Nat := 118140960795 + 6868968 * 2 ^ 59
def prefixEnd_6868968 : Nat := 4983230072969 + 3 ^ 40 * 6868968 * 2
def baseEnd_6868968 : Nat := 3527082184352786364810197

theorem tailTrace_6868968 : CollatzResearch.WordTrace tailWord_6868968 prefixEnd_6868968 3527082184352786364810197 := by
  unfold tailWord_6868968
  simp only [CollatzResearch.WordTrace]
  refine ⟨125265922489454768591075779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167021229985939691454767705 125265922489454768591075779)
  ·
    refine ⟨187898883734182152886613669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125265922489454768591075779 187898883734182152886613669)
    ·
      refine ⟨35231040700159153666240063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187898883734182152886613669 35231040700159153666240063)
      ·
        refine ⟨52846561050238730499360095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35231040700159153666240063 52846561050238730499360095)
        ·
          refine ⟨79269841575358095749040143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52846561050238730499360095 79269841575358095749040143)
          ·
            refine ⟨118904762363037143623560215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79269841575358095749040143 118904762363037143623560215)
            ·
              refine ⟨178357143544555715435340323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118904762363037143623560215 178357143544555715435340323)
              ·
                refine ⟨267535715316833573153010485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178357143544555715435340323 267535715316833573153010485)
                ·
                  refine ⟨25081473310953147483094733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267535715316833573153010485 25081473310953147483094733)
                  ·
                    refine ⟨9405552491607430306160525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25081473310953147483094733 9405552491607430306160525)
                    ·
                      refine ⟨3527082184352786364810197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405552491607430306160525 3527082184352786364810197)
                      ·
                        rfl

theorem cell23_6868968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6868968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868968 prefixEnd_6868968 := by exact prefixLift 6868968
  have htrace : WordTrace (prefixWord ++ tailWord_6868968) baseStart_6868968 baseEnd_6868968 := by
    simpa [prefixWord, tailWord_6868968, baseEnd_6868968] using wordTrace_append hprefix tailTrace_6868968
  have hstable : (prefixWord ++ tailWord_6868968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868968).length < 2 ^ (prefixWord ++ tailWord_6868968).sum := by decide
  have hdescent : baseEnd_6868968 < baseStart_6868968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868982 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6868982 : Nat := 118140960795 + 6868982 * 2 ^ 59
def prefixEnd_6868982 : Nat := 4983230072969 + 3 ^ 40 * 6868982 * 2
def baseEnd_6868982 : Nat := 3527089373081949310035133

theorem tailTrace_6868982 : CollatzResearch.WordTrace tailWord_6868982 prefixEnd_6868982 3527089373081949310035133 := by
  unfold tailWord_6868982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658272225053676098322575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167021570400572545048774133 15658272225053676098322575)
  ·
    refine ⟨23487408337580514147483863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15658272225053676098322575 23487408337580514147483863)
    ·
      refine ⟨35231112506370771221225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23487408337580514147483863 35231112506370771221225795)
      ·
        refine ⟨52846668759556156831838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35231112506370771221225795 52846668759556156831838693)
        ·
          refine ⟨9908750392416779405969755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52846668759556156831838693 9908750392416779405969755)
          ·
            refine ⟨14863125588625169108954633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9908750392416779405969755 14863125588625169108954633)
            ·
              refine ⟨11147344191468876831715975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14863125588625169108954633 11147344191468876831715975)
              ·
                refine ⟨16721016287203315247573963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147344191468876831715975 16721016287203315247573963)
                ·
                  refine ⟨25081524430804972871360945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721016287203315247573963 25081524430804972871360945)
                  ·
                    refine ⟨18811143323103729653520709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25081524430804972871360945 18811143323103729653520709)
                    ·
                      refine ⟨3527089373081949310035133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18811143323103729653520709 3527089373081949310035133)
                      ·
                        rfl

theorem cell23_6868982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6868982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868982 prefixEnd_6868982 := by exact prefixLift 6868982
  have htrace : WordTrace (prefixWord ++ tailWord_6868982) baseStart_6868982 baseEnd_6868982 := by
    simpa [prefixWord, tailWord_6868982, baseEnd_6868982] using wordTrace_append hprefix tailTrace_6868982
  have hstable : (prefixWord ++ tailWord_6868982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868982).length < 2 ^ (prefixWord ++ tailWord_6868982).sum := by decide
  have hdescent : baseEnd_6868982 < baseStart_6868982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6868985 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_6868985 : Nat := 118140960795 + 6868985 * 2 ^ 59
def prefixEnd_6868985 : Nat := 4983230072969 + 3 ^ 40 * 6868985 * 2
def baseEnd_6868985 : Nat := 3527090913523912798297619

theorem tailTrace_6868985 : CollatzResearch.WordTrace tailWord_6868985 prefixEnd_6868985 3527090913523912798297619 := by
  unfold tailWord_6868985
  simp only [CollatzResearch.WordTrace]
  refine ⟨250532465019847949085520409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167021643346565299390346939 250532465019847949085520409)
  ·
    refine ⟨187899348764885961814140307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250532465019847949085520409 187899348764885961814140307)
    ·
      refine ⟨281849023147328942721210461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187899348764885961814140307 281849023147328942721210461)
      ·
        refine ⟨105693383680248353520453923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281849023147328942721210461 105693383680248353520453923)
        ·
          refine ⟨158540075520372530280680885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105693383680248353520453923 158540075520372530280680885)
          ·
            refine ⟨14863132080034924713813833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158540075520372530280680885 14863132080034924713813833)
            ·
              refine ⟨11147349060026193535360375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14863132080034924713813833 11147349060026193535360375)
              ·
                refine ⟨16721023590039290303040563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147349060026193535360375 16721023590039290303040563)
                ·
                  refine ⟨25081535385058935454560845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721023590039290303040563 25081535385058935454560845)
                  ·
                    refine ⟨9405575769397100795460317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25081535385058935454560845 9405575769397100795460317)
                    ·
                      refine ⟨3527090913523912798297619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405575769397100795460317 3527090913523912798297619)
                      ·
                        rfl

theorem cell23_6868985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_6868985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6868985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6868985 prefixEnd_6868985 := by exact prefixLift 6868985
  have htrace : WordTrace (prefixWord ++ tailWord_6868985) baseStart_6868985 baseEnd_6868985 := by
    simpa [prefixWord, tailWord_6868985, baseEnd_6868985] using wordTrace_append hprefix tailTrace_6868985
  have hstable : (prefixWord ++ tailWord_6868985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6868985).length < 2 ^ (prefixWord ++ tailWord_6868985).sum := by decide
  have hdescent : baseEnd_6868985 < baseStart_6868985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6868985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869018 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_6869018 : Nat := 118140960795 + 6869018 * 2 ^ 59
def prefixEnd_6869018 : Nat := 4983230072969 + 3 ^ 40 * 6869018 * 2
def baseEnd_6869018 : Nat := 1175702619461837056394989

theorem tailTrace_6869018 : CollatzResearch.WordTrace tailWord_6869018 prefixEnd_6869018 1175702619461837056394989 := by
  unfold tailWord_6869018
  simp only [CollatzResearch.WordTrace]
  refine ⟨62633417157182098930367927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167022445752485597147647805 62633417157182098930367927)
  ·
    refine ⟨93950125735773148395551891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62633417157182098930367927 93950125735773148395551891)
    ·
      refine ⟨140925188603659722593327837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93950125735773148395551891 140925188603659722593327837)
      ·
        refine ⟨52846945726372395972497939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140925188603659722593327837 52846945726372395972497939)
        ·
          refine ⟨79270418589558593958746909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52846945726372395972497939 79270418589558593958746909)
          ·
            refine ⟨29726406971084472734530091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79270418589558593958746909 29726406971084472734530091)
            ·
              refine ⟨44589610456626709101795137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29726406971084472734530091 44589610456626709101795137)
              ·
                refine ⟨33442207842470031826346353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44589610456626709101795137 33442207842470031826346353)
                ·
                  refine ⟨25081655881852523869759765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33442207842470031826346353 25081655881852523869759765)
                  ·
                    refine ⟨1175702619461837056394989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25081655881852523869759765 1175702619461837056394989)
                    ·
                      rfl

theorem cell23_6869018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_6869018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869018 prefixEnd_6869018 := by exact prefixLift 6869018
  have htrace : WordTrace (prefixWord ++ tailWord_6869018) baseStart_6869018 baseEnd_6869018 := by
    simpa [prefixWord, tailWord_6869018, baseEnd_6869018] using wordTrace_append hprefix tailTrace_6869018
  have hstable : (prefixWord ++ tailWord_6869018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869018).length < 2 ^ (prefixWord ++ tailWord_6869018).sum := by decide
  have hdescent : baseEnd_6869018 < baseStart_6869018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869042 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_6869042 : Nat := 118140960795 + 6869042 * 2 ^ 59
def prefixEnd_6869042 : Nat := 4983230072969 + 3 ^ 40 * 6869042 * 2
def baseEnd_6869042 : Nat := 3527120181921219075284857

theorem tailTrace_6869042 : CollatzResearch.WordTrace tailWord_6869042 prefixEnd_6869042 3527120181921219075284857 := by
  unfold tailWord_6869042
  simp only [CollatzResearch.WordTrace]
  refine ⟨62633635995160361955086345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167023029320427631880230253 62633635995160361955086345)
  ·
    refine ⟨46975226996370271466314759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62633635995160361955086345 46975226996370271466314759)
    ·
      refine ⟨70462840494555407199472139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46975226996370271466314759 70462840494555407199472139)
      ·
        refine ⟨105694260741833110799208209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70462840494555407199472139 105694260741833110799208209)
        ·
          refine ⟨79270695556374833099406157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105694260741833110799208209 79270695556374833099406157)
          ·
            refine ⟨29726510833640562412277309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79270695556374833099406157 29726510833640562412277309)
            ·
              refine ⟨11147441562615210904603991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29726510833640562412277309 11147441562615210904603991)
              ·
                refine ⟨16721162343922816356905987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147441562615210904603991 16721162343922816356905987)
                ·
                  refine ⟨25081743515884224535358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721162343922816356905987 25081743515884224535358981)
                  ·
                    refine ⟨4702826909228292100379809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25081743515884224535358981 4702826909228292100379809)
                    ·
                      refine ⟨3527120181921219075284857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702826909228292100379809 3527120181921219075284857)
                      ·
                        rfl

theorem cell23_6869042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_6869042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869042 prefixEnd_6869042 := by exact prefixLift 6869042
  have htrace : WordTrace (prefixWord ++ tailWord_6869042) baseStart_6869042 baseEnd_6869042 := by
    simpa [prefixWord, tailWord_6869042, baseEnd_6869042] using wordTrace_append hprefix tailTrace_6869042
  have hstable : (prefixWord ++ tailWord_6869042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869042).length < 2 ^ (prefixWord ++ tailWord_6869042).sum := by decide
  have hdescent : baseEnd_6869042 < baseStart_6869042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869062 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6869062 : Nat := 118140960795 + 6869062 * 2 ^ 59
def prefixEnd_6869062 : Nat := 4983230072969 + 3 ^ 40 * 6869062 * 2
def baseEnd_6869062 : Nat := 3527130451534308997034765

theorem tailTrace_6869062 : CollatzResearch.WordTrace tailWord_6869062 prefixEnd_6869062 3527130451534308997034765 := by
  unfold tailWord_6869062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829227295017780976127295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167023515627045994157382293 7829227295017780976127295)
  ·
    refine ⟨11743840942526671464190943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7829227295017780976127295 11743840942526671464190943)
    ·
      refine ⟨17615761413790007196286415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11743840942526671464190943 17615761413790007196286415)
      ·
        refine ⟨26423642120685010794429623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17615761413790007196286415 26423642120685010794429623)
        ·
          refine ⟨39635463181027516191644435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26423642120685010794429623 39635463181027516191644435)
          ·
            refine ⟨59453194771541274287466653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39635463181027516191644435 59453194771541274287466653)
            ·
              refine ⟨22294948039327977857799995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59453194771541274287466653 22294948039327977857799995)
              ·
                refine ⟨33442422058991966786699993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22294948039327977857799995 33442422058991966786699993)
                ·
                  refine ⟨25081816544243975090024995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33442422058991966786699993 25081816544243975090024995)
                  ·
                    refine ⟨37622724816365962635037493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25081816544243975090024995 37622724816365962635037493)
                    ·
                      refine ⟨3527130451534308997034765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37622724816365962635037493 3527130451534308997034765)
                      ·
                        rfl

theorem cell23_6869062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6869062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869062 prefixEnd_6869062 := by exact prefixLift 6869062
  have htrace : WordTrace (prefixWord ++ tailWord_6869062) baseStart_6869062 baseEnd_6869062 := by
    simpa [prefixWord, tailWord_6869062, baseEnd_6869062] using wordTrace_append hprefix tailTrace_6869062
  have hstable : (prefixWord ++ tailWord_6869062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869062).length < 2 ^ (prefixWord ++ tailWord_6869062).sum := by decide
  have hdescent : baseEnd_6869062 < baseStart_6869062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869082 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_6869082 : Nat := 118140960795 + 6869082 * 2 ^ 59
def prefixEnd_6869082 : Nat := 4983230072969 + 3 ^ 40 * 6869082 * 2
def baseEnd_6869082 : Nat := 391904524571933213198297

theorem tailTrace_6869082 : CollatzResearch.WordTrace tailWord_6869082 prefixEnd_6869082 391904524571933213198297 := by
  unfold tailWord_6869082
  simp only [CollatzResearch.WordTrace]
  refine ⟨62634000725124133662950375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167024001933664356434534333 62634000725124133662950375)
  ·
    refine ⟨93951001087686200494425563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62634000725124133662950375 93951001087686200494425563)
    ·
      refine ⟨140926501631529300741638345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93951001087686200494425563 140926501631529300741638345)
      ·
        refine ⟨105694876223646975556228759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140926501631529300741638345 105694876223646975556228759)
        ·
          refine ⟨158542314335470463334343139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105694876223646975556228759 158542314335470463334343139)
          ·
            refine ⟨237813471503205695001514709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158542314335470463334343139 237813471503205695001514709)
            ·
              refine ⟨5573753238356383476598001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237813471503205695001514709 5573753238356383476598001)
              ·
                refine ⟨4180314928767287607448501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5573753238356383476598001 4180314928767287607448501)
                ·
                  refine ⟨391904524571933213198297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4180314928767287607448501 391904524571933213198297)
                  ·
                    rfl

theorem cell23_6869082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_6869082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869082 prefixEnd_6869082 := by exact prefixLift 6869082
  have htrace : WordTrace (prefixWord ++ tailWord_6869082) baseStart_6869082 baseEnd_6869082 := by
    simpa [prefixWord, tailWord_6869082, baseEnd_6869082] using wordTrace_append hprefix tailTrace_6869082
  have hstable : (prefixWord ++ tailWord_6869082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869082).length < 2 ^ (prefixWord ++ tailWord_6869082).sum := by decide
  have hdescent : baseEnd_6869082 < baseStart_6869082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869088 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_6869088 : Nat := 118140960795 + 6869088 * 2 ^ 59
def prefixEnd_6869088 : Nat := 4983230072969 + 3 ^ 40 * 6869088 * 2
def baseEnd_6869088 : Nat := 3527143802031325895309645

theorem tailTrace_6869088 : CollatzResearch.WordTrace tailWord_6869088 prefixEnd_6869088 3527143802031325895309645 := by
  unfold tailWord_6869088
  simp only [CollatzResearch.WordTrace]
  refine ⟨125268110869237398838259959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167024147825649865117679945 125268110869237398838259959)
  ·
    refine ⟨187902166303856098257389939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125268110869237398838259959 187902166303856098257389939)
    ·
      refine ⟨281853249455784147386084909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187902166303856098257389939 281853249455784147386084909)
      ·
        refine ⟨105694968545919055269781841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281853249455784147386084909 105694968545919055269781841)
        ·
          refine ⟨79271226409439291452336381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105694968545919055269781841 79271226409439291452336381)
          ·
            refine ⟨29726709903539734294626143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79271226409439291452336381 29726709903539734294626143)
            ·
              refine ⟨44590064855309601441939215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29726709903539734294626143 44590064855309601441939215)
              ·
                refine ⟨66885097282964402162908823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44590064855309601441939215 66885097282964402162908823)
                ·
                  refine ⟨100327645924446603244363235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66885097282964402162908823 100327645924446603244363235)
                  ·
                    refine ⟨150491468886669904866544853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100327645924446603244363235 150491468886669904866544853)
                    ·
                      refine ⟨3527143802031325895309645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150491468886669904866544853 3527143802031325895309645)
                      ·
                        rfl

theorem cell23_6869088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_6869088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869088 prefixEnd_6869088 := by exact prefixLift 6869088
  have htrace : WordTrace (prefixWord ++ tailWord_6869088) baseStart_6869088 baseEnd_6869088 := by
    simpa [prefixWord, tailWord_6869088, baseEnd_6869088] using wordTrace_append hprefix tailTrace_6869088
  have hstable : (prefixWord ++ tailWord_6869088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869088).length < 2 ^ (prefixWord ++ tailWord_6869088).sum := by decide
  have hdescent : baseEnd_6869088 < baseStart_6869088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869115 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 6, 4, 2]
def baseStart_6869115 : Nat := 118140960795 + 6869115 * 2 ^ 59
def prefixEnd_6869115 : Nat := 4983230072969 + 3 ^ 40 * 6869115 * 2
def baseEnd_6869115 : Nat := 3527157666008997289672021

theorem tailTrace_6869115 : CollatzResearch.WordTrace tailWord_6869115 prefixEnd_6869115 3527157666008997289672021 := by
  unfold tailWord_6869115
  simp only [CollatzResearch.WordTrace]
  refine ⟨250537206509376981287752799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167024804339584654191835199 250537206509376981287752799)
  ·
    refine ⟨375805809764065471931629199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250537206509376981287752799 375805809764065471931629199)
    ·
      refine ⟨563708714646098207897443799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375805809764065471931629199 563708714646098207897443799)
      ·
        refine ⟨845563071969147311846165699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563708714646098207897443799 845563071969147311846165699)
        ·
          refine ⟨1268344607953720967769248549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845563071969147311846165699 1268344607953720967769248549)
          ·
            refine ⟨237814613991322681456734103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1268344607953720967769248549 237814613991322681456734103)
            ·
              refine ⟨356721920986984022185101155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237814613991322681456734103 356721920986984022185101155)
              ·
                refine ⟨535082881480476033277651733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356721920986984022185101155 535082881480476033277651733)
                ·
                  refine ⟨25082010069397314059889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 535082881480476033277651733 25082010069397314059889925)
                  ·
                    refine ⟨4702876888011996386229361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25082010069397314059889925 4702876888011996386229361)
                    ·
                      refine ⟨3527157666008997289672021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702876888011996386229361 3527157666008997289672021)
                      ·
                        rfl

theorem cell23_6869115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4, 2].length) (baseStart_6869115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869115 prefixEnd_6869115 := by exact prefixLift 6869115
  have htrace : WordTrace (prefixWord ++ tailWord_6869115) baseStart_6869115 baseEnd_6869115 := by
    simpa [prefixWord, tailWord_6869115, baseEnd_6869115] using wordTrace_append hprefix tailTrace_6869115
  have hstable : (prefixWord ++ tailWord_6869115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869115).length < 2 ^ (prefixWord ++ tailWord_6869115).sum := by decide
  have hdescent : baseEnd_6869115 < baseStart_6869115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869159 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6869159 : Nat := 118140960795 + 6869159 * 2 ^ 59
def prefixEnd_6869159 : Nat := 4983230072969 + 3 ^ 40 * 6869159 * 2
def baseEnd_6869159 : Nat := 1175726753052598372507273

theorem tailTrace_6869159 : CollatzResearch.WordTrace tailWord_6869159 prefixEnd_6869159 1175726753052598372507273 := by
  unfold tailWord_6869159
  simp only [CollatzResearch.WordTrace]
  refine ⟨250538811321217576802354531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167025874214145051201569687 250538811321217576802354531)
  ·
    refine ⟨375808216981826365203531797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250538811321217576802354531 375808216981826365203531797)
    ·
      refine ⟨17616010171023110868915553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 375808216981826365203531797 17616010171023110868915553)
      ·
        refine ⟨13212007628267333151686665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17616010171023110868915553 13212007628267333151686665)
        ·
          refine ⟨9909005721200499863764999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13212007628267333151686665 9909005721200499863764999)
          ·
            refine ⟨14863508581800749795647499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9909005721200499863764999 14863508581800749795647499)
            ·
              refine ⟨22295262872701124693471249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14863508581800749795647499 22295262872701124693471249)
              ·
                refine ⟨16721447154525843520103437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22295262872701124693471249 16721447154525843520103437)
                ·
                  refine ⟨6270542682947191320038789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16721447154525843520103437 6270542682947191320038789)
                  ·
                    refine ⟨1175726753052598372507273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6270542682947191320038789 1175726753052598372507273)
                    ·
                      rfl

theorem cell23_6869159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6869159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869159 prefixEnd_6869159 := by exact prefixLift 6869159
  have htrace : WordTrace (prefixWord ++ tailWord_6869159) baseStart_6869159 baseEnd_6869159 := by
    simpa [prefixWord, tailWord_6869159, baseEnd_6869159] using wordTrace_append hprefix tailTrace_6869159
  have hstable : (prefixWord ++ tailWord_6869159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869159).length < 2 ^ (prefixWord ++ tailWord_6869159).sum := by decide
  have hdescent : baseEnd_6869159 < baseStart_6869159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869192 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_6869192 : Nat := 118140960795 + 6869192 * 2 ^ 59
def prefixEnd_6869192 : Nat := 4983230072969 + 3 ^ 40 * 6869192 * 2
def baseEnd_6869192 : Nat := 3527197204019393488409167

theorem tailTrace_6869192 : CollatzResearch.WordTrace tailWord_6869192 prefixEnd_6869192 3527197204019393488409167 := by
  unfold tailWord_6869192
  simp only [CollatzResearch.WordTrace]
  refine ⟨125270007465049011719152915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167026676620065348958870553 125270007465049011719152915)
  ·
    refine ⟨187905011197573517578729373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125270007465049011719152915 187905011197573517578729373)
    ·
      refine ⟨70464379199090069092023515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187905011197573517578729373 70464379199090069092023515)
      ·
        refine ⟨105696568798635103638035273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70464379199090069092023515 105696568798635103638035273)
        ·
          refine ⟨79272426598976327728526455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105696568798635103638035273 79272426598976327728526455)
          ·
            refine ⟨118908639898464491592789683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79272426598976327728526455 118908639898464491592789683)
            ·
              refine ⟨178362959847696737389184525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118908639898464491592789683 178362959847696737389184525)
              ·
                refine ⟨66886109942886276520944197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178362959847696737389184525 66886109942886276520944197)
                ·
                  refine ⟨12541145614291176847677037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66886109942886276520944197 12541145614291176847677037)
                  ·
                    refine ⟨4702929605359191317878889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12541145614291176847677037 4702929605359191317878889)
                    ·
                      refine ⟨3527197204019393488409167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702929605359191317878889 3527197204019393488409167)
                      ·
                        rfl

theorem cell23_6869192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_6869192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869192 prefixEnd_6869192 := by exact prefixLift 6869192
  have htrace : WordTrace (prefixWord ++ tailWord_6869192) baseStart_6869192 baseEnd_6869192 := by
    simpa [prefixWord, tailWord_6869192, baseEnd_6869192] using wordTrace_append hprefix tailTrace_6869192
  have hstable : (prefixWord ++ tailWord_6869192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869192).length < 2 ^ (prefixWord ++ tailWord_6869192).sum := by decide
  have hdescent : baseEnd_6869192 < baseStart_6869192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869199 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 1, 1, 3]
def baseStart_6869199 : Nat := 118140960795 + 6869199 * 2 ^ 59
def prefixEnd_6869199 : Nat := 4983230072969 + 3 ^ 40 * 6869199 * 2
def baseEnd_6869199 : Nat := 3527200798383974961021635

theorem tailTrace_6869199 : CollatzResearch.WordTrace tailWord_6869199 prefixEnd_6869199 3527200798383974961021635 := by
  unfold tailWord_6869199
  simp only [CollatzResearch.WordTrace]
  refine ⟨250540270241072663633810651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167026846827381775755873767 250540270241072663633810651)
  ·
    refine ⟨375810405361608995450715977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250540270241072663633810651 375810405361608995450715977)
    ·
      refine ⟨281857804021206746588036983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375810405361608995450715977 281857804021206746588036983)
      ·
        refine ⟨422786706031810119882055475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281857804021206746588036983 422786706031810119882055475)
        ·
          refine ⟨634180059047715179823083213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422786706031810119882055475 634180059047715179823083213)
          ·
            refine ⟨237817522142893192433656205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634180059047715179823083213 237817522142893192433656205)
            ·
              refine ⟨89181570803584947162621077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237817522142893192433656205 89181570803584947162621077)
              ·
                refine ⟨4180386131418044398247863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89181570803584947162621077 4180386131418044398247863)
                ·
                  refine ⟨6270579197127066597371795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180386131418044398247863 6270579197127066597371795)
                  ·
                    refine ⟨9405868795690599896057693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270579197127066597371795 9405868795690599896057693)
                    ·
                      refine ⟨3527200798383974961021635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405868795690599896057693 3527200798383974961021635)
                      ·
                        rfl

theorem cell23_6869199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 1, 3].length) (baseStart_6869199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869199 prefixEnd_6869199 := by exact prefixLift 6869199
  have htrace : WordTrace (prefixWord ++ tailWord_6869199) baseStart_6869199 baseEnd_6869199 := by
    simpa [prefixWord, tailWord_6869199, baseEnd_6869199] using wordTrace_append hprefix tailTrace_6869199
  have hstable : (prefixWord ++ tailWord_6869199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869199).length < 2 ^ (prefixWord ++ tailWord_6869199).sum := by decide
  have hdescent : baseEnd_6869199 < baseStart_6869199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869206 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6869206 : Nat := 118140960795 + 6869206 * 2 ^ 59
def prefixEnd_6869206 : Nat := 4983230072969 + 3 ^ 40 * 6869206 * 2
def baseEnd_6869206 : Nat := 391911599194284048181567

theorem tailTrace_6869206 : CollatzResearch.WordTrace tailWord_6869206 prefixEnd_6869206 391911599194284048181567 := by
  unfold tailWord_6869206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658782847002956489332217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167027017034698202552876981 15658782847002956489332217)
  ·
    refine ⟨11744087135252217366999163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15658782847002956489332217 11744087135252217366999163)
    ·
      refine ⟨17616130702878326050498745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11744087135252217366999163 17616130702878326050498745)
      ·
        refine ⟨13212098027158744537874059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17616130702878326050498745 13212098027158744537874059)
        ·
          refine ⟨19818147040738116806811089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13212098027158744537874059 19818147040738116806811089)
          ·
            refine ⟨14863610280553587605108317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19818147040738116806811089 14863610280553587605108317)
            ·
              refine ⟨5573853855207595351915619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14863610280553587605108317 5573853855207595351915619)
              ·
                refine ⟨8360780782811393027873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573853855207595351915619 8360780782811393027873429)
                ·
                  refine ⟨391911599194284048181567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8360780782811393027873429 391911599194284048181567)
                  ·
                    rfl

theorem cell23_6869206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6869206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869206 prefixEnd_6869206 := by exact prefixLift 6869206
  have htrace : WordTrace (prefixWord ++ tailWord_6869206) baseStart_6869206 baseEnd_6869206 := by
    simpa [prefixWord, tailWord_6869206, baseEnd_6869206] using wordTrace_append hprefix tailTrace_6869206
  have hstable : (prefixWord ++ tailWord_6869206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869206).length < 2 ^ (prefixWord ++ tailWord_6869206).sum := by decide
  have hdescent : baseEnd_6869206 < baseStart_6869206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869235 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_6869235 : Nat := 118140960795 + 6869235 * 2 ^ 59
def prefixEnd_6869235 : Nat := 4983230072969 + 3 ^ 40 * 6869235 * 2
def baseEnd_6869235 : Nat := 3527219283687536820171469

theorem tailTrace_6869235 : CollatzResearch.WordTrace tailWord_6869235 prefixEnd_6869235 3527219283687536820171469 := by
  unfold tailWord_6869235
  simp only [CollatzResearch.WordTrace]
  refine ⟨250541583268942241782121159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167027722179294827854747439 250541583268942241782121159)
  ·
    refine ⟨375812374903413362673181739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250541583268942241782121159 375812374903413362673181739)
    ·
      refine ⟨563718562355120044009772609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375812374903413362673181739 563718562355120044009772609)
      ·
        refine ⟨422788921766340033007329457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563718562355120044009772609 422788921766340033007329457)
        ·
          refine ⟨317091691324755024755497093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422788921766340033007329457 317091691324755024755497093)
          ·
            refine ⟨59454692123391567141655705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317091691324755024755497093 59454692123391567141655705)
            ·
              refine ⟨44591019092543675356241779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59454692123391567141655705 44591019092543675356241779)
              ·
                refine ⟨66886528638815513034362669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44591019092543675356241779 66886528638815513034362669)
                ·
                  refine ⟨25082448239555817387886001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66886528638815513034362669 25082448239555817387886001)
                  ·
                    refine ⟨18811836179666863040914501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25082448239555817387886001 18811836179666863040914501)
                    ·
                      refine ⟨3527219283687536820171469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18811836179666863040914501 3527219283687536820171469)
                      ·
                        rfl

theorem cell23_6869235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_6869235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869235 prefixEnd_6869235 := by exact prefixLift 6869235
  have htrace : WordTrace (prefixWord ++ tailWord_6869235) baseStart_6869235 baseEnd_6869235 := by
    simpa [prefixWord, tailWord_6869235, baseEnd_6869235] using wordTrace_append hprefix tailTrace_6869235
  have hstable : (prefixWord ++ tailWord_6869235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869235).length < 2 ^ (prefixWord ++ tailWord_6869235).sum := by decide
  have hdescent : baseEnd_6869235 < baseStart_6869235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869242 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_6869242 : Nat := 118140960795 + 6869242 * 2 ^ 59
def prefixEnd_6869242 : Nat := 4983230072969 + 3 ^ 40 * 6869242 * 2
def baseEnd_6869242 : Nat := 3527222878052118292783937

theorem tailTrace_6869242 : CollatzResearch.WordTrace tailWord_6869242 prefixEnd_6869242 3527222878052118292783937 := by
  unfold tailWord_6869242
  simp only [CollatzResearch.WordTrace]
  refine ⟨62635459644979220494406495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167027892386611254651750653 62635459644979220494406495)
  ·
    refine ⟨93953189467468830741609743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62635459644979220494406495 93953189467468830741609743)
    ·
      refine ⟨140929784201203246112414615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93953189467468830741609743 140929784201203246112414615)
      ·
        refine ⟨211394676301804869168621923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140929784201203246112414615 211394676301804869168621923)
        ·
          refine ⟨317092014452707303752932885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211394676301804869168621923 317092014452707303752932885)
          ·
            refine ⟨14863688177470654863418729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317092014452707303752932885 14863688177470654863418729)
            ·
              refine ⟨11147766133102991147564047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14863688177470654863418729 11147766133102991147564047)
              ·
                refine ⟨16721649199654486721346071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147766133102991147564047 16721649199654486721346071)
                ·
                  refine ⟨25082473799481730082019107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721649199654486721346071 25082473799481730082019107)
                  ·
                    refine ⟨37623710699222595123028661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25082473799481730082019107 37623710699222595123028661)
                    ·
                      refine ⟨3527222878052118292783937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37623710699222595123028661 3527222878052118292783937)
                      ·
                        rfl

theorem cell23_6869242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_6869242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869242 prefixEnd_6869242 := by exact prefixLift 6869242
  have htrace : WordTrace (prefixWord ++ tailWord_6869242) baseStart_6869242 baseEnd_6869242 := by
    simpa [prefixWord, tailWord_6869242, baseEnd_6869242] using wordTrace_append hprefix tailTrace_6869242
  have hstable : (prefixWord ++ tailWord_6869242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869242).length < 2 ^ (prefixWord ++ tailWord_6869242).sum := by decide
  have hdescent : baseEnd_6869242 < baseStart_6869242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869250 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_6869250 : Nat := 118140960795 + 6869250 * 2 ^ 59
def prefixEnd_6869250 : Nat := 4983230072969 + 3 ^ 40 * 6869250 * 2
def baseEnd_6869250 : Nat := 3527226985897354261483901

theorem tailTrace_6869250 : CollatzResearch.WordTrace tailWord_6869250 prefixEnd_6869250 3527226985897354261483901 := by
  unfold tailWord_6869250
  simp only [CollatzResearch.WordTrace]
  refine ⟨62635532590971974835979301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167028086909258599562611469 62635532590971974835979301)
  ·
    refine ⟨11744162360807245281746119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62635532590971974835979301 11744162360807245281746119)
    ·
      refine ⟨17616243541210867922619179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11744162360807245281746119 17616243541210867922619179)
      ·
        refine ⟨26424365311816301883928769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17616243541210867922619179 26424365311816301883928769)
        ·
          refine ⟨19818273983862226412946577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26424365311816301883928769 19818273983862226412946577)
          ·
            refine ⟨14863705487896669809709933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19818273983862226412946577 14863705487896669809709933)
            ·
              refine ⟨5573889557961251178641225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14863705487896669809709933 5573889557961251178641225)
              ·
                refine ⟨4180417168470938383980919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5573889557961251178641225 4180417168470938383980919)
                ·
                  refine ⟨6270625752706407575971379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180417168470938383980919 6270625752706407575971379)
                  ·
                    refine ⟨9405938629059611363957069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270625752706407575971379 9405938629059611363957069)
                    ·
                      refine ⟨3527226985897354261483901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405938629059611363957069 3527226985897354261483901)
                      ·
                        rfl

theorem cell23_6869250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_6869250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869250 prefixEnd_6869250 := by exact prefixLift 6869250
  have htrace : WordTrace (prefixWord ++ tailWord_6869250) baseStart_6869250 baseEnd_6869250 := by
    simpa [prefixWord, tailWord_6869250, baseEnd_6869250] using wordTrace_append hprefix tailTrace_6869250
  have hstable : (prefixWord ++ tailWord_6869250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869250).length < 2 ^ (prefixWord ++ tailWord_6869250).sum := by decide
  have hdescent : baseEnd_6869250 < baseStart_6869250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869256 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_6869256 : Nat := 118140960795 + 6869256 * 2 ^ 59
def prefixEnd_6869256 : Nat := 4983230072969 + 3 ^ 40 * 6869256 * 2
def baseEnd_6869256 : Nat := 3527230066781281238008873

theorem tailTrace_6869256 : CollatzResearch.WordTrace tailWord_6869256 prefixEnd_6869256 3527230066781281238008873 := by
  unfold tailWord_6869256
  simp only [CollatzResearch.WordTrace]
  refine ⟨125271174600933081184317811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167028232801244108245757081 125271174600933081184317811)
  ·
    refine ⟨187906761901399621776476717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125271174600933081184317811 187906761901399621776476717)
    ·
      refine ⟨70465035713024858166178769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187906761901399621776476717 70465035713024858166178769)
      ·
        refine ⟨52848776784768643624634077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70465035713024858166178769 52848776784768643624634077)
        ·
          refine ⟨19818291294288241359237779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52848776784768643624634077 19818291294288241359237779)
          ·
            refine ⟨29727436941432362038856669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19818291294288241359237779 29727436941432362038856669)
            ·
              refine ⟨11147788853037135764571251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29727436941432362038856669 11147788853037135764571251)
              ·
                refine ⟨16721683279555703646856877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147788853037135764571251 16721683279555703646856877)
                ·
                  refine ⟨6270631229833388867571329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16721683279555703646856877 6270631229833388867571329)
                  ·
                    refine ⟨4702973422375041650678497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6270631229833388867571329 4702973422375041650678497)
                    ·
                      refine ⟨3527230066781281238008873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4702973422375041650678497 3527230066781281238008873)
                      ·
                        rfl

theorem cell23_6869256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_6869256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869256 prefixEnd_6869256 := by exact prefixLift 6869256
  have htrace : WordTrace (prefixWord ++ tailWord_6869256) baseStart_6869256 baseEnd_6869256 := by
    simpa [prefixWord, tailWord_6869256, baseEnd_6869256] using wordTrace_append hprefix tailTrace_6869256
  have hstable : (prefixWord ++ tailWord_6869256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869256).length < 2 ^ (prefixWord ++ tailWord_6869256).sum := by decide
  have hdescent : baseEnd_6869256 < baseStart_6869256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869272 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_6869272 : Nat := 118140960795 + 6869272 * 2 ^ 59
def prefixEnd_6869272 : Nat := 4983230072969 + 3 ^ 40 * 6869272 * 2
def baseEnd_6869272 : Nat := 3527238282471753175408799

theorem tailTrace_6869272 : CollatzResearch.WordTrace tailWord_6869272 prefixEnd_6869272 3527238282471753175408799 := by
  unfold tailWord_6869272
  simp only [CollatzResearch.WordTrace]
  refine ⟨125271466384904098550609035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167028621846538798067478713 125271466384904098550609035)
  ·
    refine ⟨187907199577356147825913553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125271466384904098550609035 187907199577356147825913553)
    ·
      refine ⟨140930399683017110869435165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187907199577356147825913553 140930399683017110869435165)
      ·
        refine ⟨52848899881131416576038187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140930399683017110869435165 52848899881131416576038187)
        ·
          refine ⟨79273349821697124864057281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52848899881131416576038187 79273349821697124864057281)
          ·
            refine ⟨59455012366272843648042961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79273349821697124864057281 59455012366272843648042961)
            ·
              refine ⟨44591259274704632736032221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59455012366272843648042961 44591259274704632736032221)
              ·
                refine ⟨16721722228014237276012083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44591259274704632736032221 16721722228014237276012083)
                ·
                  refine ⟨25082583342021355914018125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721722228014237276012083 25082583342021355914018125)
                  ·
                    refine ⟨9405968753258008467756797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25082583342021355914018125 9405968753258008467756797)
                    ·
                      refine ⟨3527238282471753175408799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9405968753258008467756797 3527238282471753175408799)
                      ·
                        rfl

theorem cell23_6869272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_6869272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869272 prefixEnd_6869272 := by exact prefixLift 6869272
  have htrace : WordTrace (prefixWord ++ tailWord_6869272) baseStart_6869272 baseEnd_6869272 := by
    simpa [prefixWord, tailWord_6869272, baseEnd_6869272] using wordTrace_append hprefix tailTrace_6869272
  have hstable : (prefixWord ++ tailWord_6869272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869272).length < 2 ^ (prefixWord ++ tailWord_6869272).sum := by decide
  have hdescent : baseEnd_6869272 < baseStart_6869272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869293 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6869293 : Nat := 118140960795 + 6869293 * 2 ^ 59
def prefixEnd_6869293 : Nat := 4983230072969 + 3 ^ 40 * 6869293 * 2
def baseEnd_6869293 : Nat := 3527249065565497593246203

theorem tailTrace_6869293 : CollatzResearch.WordTrace tailWord_6869293 prefixEnd_6869293 3527249065565497593246203 := by
  unfold tailWord_6869293
  simp only [CollatzResearch.WordTrace]
  refine ⟨250543698702732117687732533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167029132468488078458488355 250543698702732117687732533)
  ·
    refine ⟨23488471753381136033224925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250543698702732117687732533 23488471753381136033224925)
    ·
      refine ⟨8808176907517926012459347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23488471753381136033224925 8808176907517926012459347)
      ·
        refine ⟨13212265361276889018689021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808176907517926012459347 13212265361276889018689021)
        ·
          refine ⟨4954599510478833382008383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13212265361276889018689021 4954599510478833382008383)
          ·
            refine ⟨7431899265718250073012575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954599510478833382008383 7431899265718250073012575)
            ·
              refine ⟨11147848898577375109518863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431899265718250073012575 11147848898577375109518863)
              ·
                refine ⟨16721773347866062664278295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147848898577375109518863 16721773347866062664278295)
                ·
                  refine ⟨25082660021799093996417443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721773347866062664278295 25082660021799093996417443)
                  ·
                    refine ⟨37623990032698640994626165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25082660021799093996417443 37623990032698640994626165)
                    ·
                      refine ⟨3527249065565497593246203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37623990032698640994626165 3527249065565497593246203)
                      ·
                        rfl

theorem cell23_6869293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6869293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869293 prefixEnd_6869293 := by exact prefixLift 6869293
  have htrace : WordTrace (prefixWord ++ tailWord_6869293) baseStart_6869293 baseEnd_6869293 := by
    simpa [prefixWord, tailWord_6869293, baseEnd_6869293] using wordTrace_append hprefix tailTrace_6869293
  have hstable : (prefixWord ++ tailWord_6869293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869293).length < 2 ^ (prefixWord ++ tailWord_6869293).sum := by decide
  have hdescent : baseEnd_6869293 < baseStart_6869293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869306 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_6869306 : Nat := 118140960795 + 6869306 * 2 ^ 59
def prefixEnd_6869306 : Nat := 4983230072969 + 3 ^ 40 * 6869306 * 2
def baseEnd_6869306 : Nat := 3527255740814006042383643

theorem tailTrace_6869306 : CollatzResearch.WordTrace tailWord_6869306 prefixEnd_6869306 3527255740814006042383643 := by
  unfold tailWord_6869306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62636043212921255226988943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167029448567790013938637181 62636043212921255226988943)
  ·
    refine ⟨93954064819381882840483415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62636043212921255226988943 93954064819381882840483415)
    ·
      refine ⟨140931097229072824260725123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93954064819381882840483415 140931097229072824260725123)
      ·
        refine ⟨211396645843609236391087685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140931097229072824260725123 211396645843609236391087685)
        ·
          refine ⟨39636871095676731823328941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211396645843609236391087685 39636871095676731823328941)
          ·
            refine ⟨14863826660878774433748353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39636871095676731823328941 14863826660878774433748353)
            ·
              refine ⟨11147869995659080825311265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14863826660878774433748353 11147869995659080825311265)
              ·
                refine ⟨8360902496744310618983449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11147869995659080825311265 8360902496744310618983449)
                ·
                  refine ⟨6270676872558232964237587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8360902496744310618983449 6270676872558232964237587)
                  ·
                    refine ⟨9406015308837349446356381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270676872558232964237587 9406015308837349446356381)
                    ·
                      refine ⟨3527255740814006042383643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9406015308837349446356381 3527255740814006042383643)
                      ·
                        rfl

theorem cell23_6869306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_6869306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869306 prefixEnd_6869306 := by exact prefixLift 6869306
  have htrace : WordTrace (prefixWord ++ tailWord_6869306) baseStart_6869306 baseEnd_6869306 := by
    simpa [prefixWord, tailWord_6869306, baseEnd_6869306] using wordTrace_append hprefix tailTrace_6869306
  have hstable : (prefixWord ++ tailWord_6869306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869306).length < 2 ^ (prefixWord ++ tailWord_6869306).sum := by decide
  have hdescent : baseEnd_6869306 < baseStart_6869306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869315 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_6869315 : Nat := 118140960795 + 6869315 * 2 ^ 59
def prefixEnd_6869315 : Nat := 4983230072969 + 3 ^ 40 * 6869315 * 2
def baseEnd_6869315 : Nat := 3527260362139896507171101

theorem tailTrace_6869315 : CollatzResearch.WordTrace tailWord_6869315 prefixEnd_6869315 3527260362139896507171101 := by
  unfold tailWord_6869315
  simp only [CollatzResearch.WordTrace]
  refine ⟨250544501108652415445033399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167029667405768276963355599 250544501108652415445033399)
  ·
    refine ⟨375816751662978623167550099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250544501108652415445033399 375816751662978623167550099)
    ·
      refine ⟨563725127494467934751325149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375816751662978623167550099 563725127494467934751325149)
      ·
        refine ⟨211396922810425475531746931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563725127494467934751325149 211396922810425475531746931)
        ·
          refine ⟨317095384215638213297620397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211396922810425475531746931 317095384215638213297620397)
          ·
            refine ⟨118910769080864329986607649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317095384215638213297620397 118910769080864329986607649)
            ·
              refine ⟨89183076810648247489955737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118910769080864329986607649 89183076810648247489955737)
              ·
                refine ⟨66887307607986185617466803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89183076810648247489955737 66887307607986185617466803)
                ·
                  refine ⟨100330961411979278426200205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66887307607986185617466803 100330961411979278426200205)
                  ·
                    refine ⟨37624110529492229409825077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100330961411979278426200205 37624110529492229409825077)
                    ·
                      refine ⟨3527260362139896507171101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37624110529492229409825077 3527260362139896507171101)
                      ·
                        rfl

theorem cell23_6869315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_6869315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869315 prefixEnd_6869315 := by exact prefixLift 6869315
  have htrace : WordTrace (prefixWord ++ tailWord_6869315) baseStart_6869315 baseEnd_6869315 := by
    simpa [prefixWord, tailWord_6869315, baseEnd_6869315] using wordTrace_append hprefix tailTrace_6869315
  have hstable : (prefixWord ++ tailWord_6869315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869315).length < 2 ^ (prefixWord ++ tailWord_6869315).sum := by decide
  have hdescent : baseEnd_6869315 < baseStart_6869315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869329 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_6869329 : Nat := 118140960795 + 6869329 * 2 ^ 59
def prefixEnd_6869329 : Nat := 4983230072969 + 3 ^ 40 * 6869329 * 2
def baseEnd_6869329 : Nat := 3527267550869059452396037

theorem tailTrace_6869329 : CollatzResearch.WordTrace tailWord_6869329 prefixEnd_6869329 3527267550869059452396037 := by
  unfold tailWord_6869329
  simp only [CollatzResearch.WordTrace]
  refine ⟨250545011730601695836043041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167030007820401130557362027 250545011730601695836043041)
  ·
    refine ⟨187908758797951271877032281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250545011730601695836043041 187908758797951271877032281)
    ·
      refine ⟨140931569098463453907774211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187908758797951271877032281 140931569098463453907774211)
      ·
        refine ⟨211397353647695180861661317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140931569098463453907774211 211397353647695180861661317)
        ·
          refine ⟨39637003808942846411561497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211397353647695180861661317 39637003808942846411561497)
          ·
            refine ⟨29727752856707134808671123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39637003808942846411561497 29727752856707134808671123)
            ·
              refine ⟨44591629285060702213006685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29727752856707134808671123 44591629285060702213006685)
              ·
                refine ⟨16721860981897763329877507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44591629285060702213006685 16721860981897763329877507)
                ·
                  refine ⟨25082791472846644994816261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721860981897763329877507 25082791472846644994816261)
                  ·
                    refine ⟨4703023401158745936528049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25082791472846644994816261 4703023401158745936528049)
                    ·
                      refine ⟨3527267550869059452396037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703023401158745936528049 3527267550869059452396037)
                      ·
                        rfl

theorem cell23_6869329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_6869329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869329 prefixEnd_6869329 := by exact prefixLift 6869329
  have htrace : WordTrace (prefixWord ++ tailWord_6869329) baseStart_6869329 baseEnd_6869329 := by
    simpa [prefixWord, tailWord_6869329, baseEnd_6869329] using wordTrace_append hprefix tailTrace_6869329
  have hstable : (prefixWord ++ tailWord_6869329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869329).length < 2 ^ (prefixWord ++ tailWord_6869329).sum := by decide
  have hdescent : baseEnd_6869329 < baseStart_6869329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869345 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6869345 : Nat := 118140960795 + 6869345 * 2 ^ 59
def prefixEnd_6869345 : Nat := 4983230072969 + 3 ^ 40 * 6869345 * 2
def baseEnd_6869345 : Nat := 3527275766559531389795963

theorem tailTrace_6869345 : CollatzResearch.WordTrace tailWord_6869345 prefixEnd_6869345 3527275766559531389795963 := by
  unfold tailWord_6869345
  simp only [CollatzResearch.WordTrace]
  refine ⟨250545595298543730568625489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167030396865695820379083659 250545595298543730568625489)
  ·
    refine ⟨187909196473907797926469117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250545595298543730568625489 187909196473907797926469117)
    ·
      refine ⟨70465948677715424222425919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187909196473907797926469117 70465948677715424222425919)
      ·
        refine ⟨105698923016573136333638879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70465948677715424222425919 105698923016573136333638879)
        ·
          refine ⟨158548384524859704500458319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105698923016573136333638879 158548384524859704500458319)
          ·
            refine ⟨237822576787289556750687479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158548384524859704500458319 237822576787289556750687479)
            ·
              refine ⟨356733865180934335126031219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237822576787289556750687479 356733865180934335126031219)
              ·
                refine ⟨535100797771401502689046829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356733865180934335126031219 535100797771401502689046829)
                ·
                  refine ⟨200662799164275563508392561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535100797771401502689046829 200662799164275563508392561)
                  ·
                    refine ⟨150497099373206672631294421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200662799164275563508392561 150497099373206672631294421)
                    ·
                      refine ⟨3527275766559531389795963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150497099373206672631294421 3527275766559531389795963)
                      ·
                        rfl

theorem cell23_6869345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6869345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869345 prefixEnd_6869345 := by exact prefixLift 6869345
  have htrace : WordTrace (prefixWord ++ tailWord_6869345) baseStart_6869345 baseEnd_6869345 := by
    simpa [prefixWord, tailWord_6869345, baseEnd_6869345] using wordTrace_append hprefix tailTrace_6869345
  have hstable : (prefixWord ++ tailWord_6869345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869345).length < 2 ^ (prefixWord ++ tailWord_6869345).sum := by decide
  have hdescent : baseEnd_6869345 < baseStart_6869345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869346 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_6869346 : Nat := 118140960795 + 6869346 * 2 ^ 59
def prefixEnd_6869346 : Nat := 4983230072969 + 3 ^ 40 * 6869346 * 2
def baseEnd_6869346 : Nat := 3527276280040185885883459

theorem tailTrace_6869346 : CollatzResearch.WordTrace tailWord_6869346 prefixEnd_6869346 3527276280040185885883459 := by
  unfold tailWord_6869346
  simp only [CollatzResearch.WordTrace]
  refine ⟨62636407942885026934852973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167030421181026738492941261 62636407942885026934852973)
  ·
    refine ⟨23488652978581885100569865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62636407942885026934852973 23488652978581885100569865)
    ·
      refine ⟨17616489733936413825427399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23488652978581885100569865 17616489733936413825427399)
      ·
        refine ⟨26424734600904620738141099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17616489733936413825427399 26424734600904620738141099)
        ·
          refine ⟨39637101901356931107211649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26424734600904620738141099 39637101901356931107211649)
          ·
            refine ⟨29727826426017698330408737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39637101901356931107211649 29727826426017698330408737)
            ·
              refine ⟨22295869819513273747806553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29727826426017698330408737 22295869819513273747806553)
              ·
                refine ⟨16721902364634955310854915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22295869819513273747806553 16721902364634955310854915)
                ·
                  refine ⟨25082853546952432966282373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16721902364634955310854915 25082853546952432966282373)
                  ·
                    refine ⟨4703035040053581181177945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25082853546952432966282373 4703035040053581181177945)
                    ·
                      refine ⟨3527276280040185885883459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703035040053581181177945 3527276280040185885883459)
                      ·
                        rfl

theorem cell23_6869346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_6869346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869346 prefixEnd_6869346 := by exact prefixLift 6869346
  have htrace : WordTrace (prefixWord ++ tailWord_6869346) baseStart_6869346 baseEnd_6869346 := by
    simpa [prefixWord, tailWord_6869346, baseEnd_6869346] using wordTrace_append hprefix tailTrace_6869346
  have hstable : (prefixWord ++ tailWord_6869346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869346).length < 2 ^ (prefixWord ++ tailWord_6869346).sum := by decide
  have hdescent : baseEnd_6869346 < baseStart_6869346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869416 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6869416 : Nat := 118140960795 + 6869416 * 2 ^ 59
def prefixEnd_6869416 : Nat := 4983230072969 + 3 ^ 40 * 6869416 * 2
def baseEnd_6869416 : Nat := 1175770741228666870669379

theorem tailTrace_6869416 : CollatzResearch.WordTrace tailWord_6869416 prefixEnd_6869416 1175770741228666870669379 := by
  unfold tailWord_6869416
  simp only [CollatzResearch.WordTrace]
  refine ⟨125274092440643254847230051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167032123254191006462973401 125274092440643254847230051)
  ·
    refine ⟨187911138660964882270845077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125274092440643254847230051 187911138660964882270845077)
    ·
      refine ⟨8808334624732728856445863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187911138660964882270845077 8808334624732728856445863)
      ·
        refine ⟨13212501937099093284668795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808334624732728856445863 13212501937099093284668795)
        ·
          refine ⟨19818752905648639927003193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13212501937099093284668795 19818752905648639927003193)
          ·
            refine ⟨14864064679236479945252395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19818752905648639927003193 14864064679236479945252395)
            ·
              refine ⟨22296097018854719917878593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14864064679236479945252395 22296097018854719917878593)
              ·
                refine ⟨16722072764141039938408945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22296097018854719917878593 16722072764141039938408945)
                ·
                  refine ⟨12541554573105779953806709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16722072764141039938408945 12541554573105779953806709)
                  ·
                    refine ⟨1175770741228666870669379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12541554573105779953806709 1175770741228666870669379)
                    ·
                      rfl

theorem cell23_6869416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6869416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869416 prefixEnd_6869416 := by exact prefixLift 6869416
  have htrace : WordTrace (prefixWord ++ tailWord_6869416) baseStart_6869416 baseEnd_6869416 := by
    simpa [prefixWord, tailWord_6869416, baseEnd_6869416] using wordTrace_append hprefix tailTrace_6869416
  have hstable : (prefixWord ++ tailWord_6869416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869416).length < 2 ^ (prefixWord ++ tailWord_6869416).sum := by decide
  have hdescent : baseEnd_6869416 < baseStart_6869416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869480 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6869480 : Nat := 118140960795 + 6869480 * 2 ^ 59
def prefixEnd_6869480 : Nat := 4983230072969 + 3 ^ 40 * 6869480 * 2
def baseEnd_6869480 : Nat := 1175781695482629453869281

theorem tailTrace_6869480 : CollatzResearch.WordTrace tailWord_6869480 prefixEnd_6869480 1175781695482629453869281 := by
  unfold tailWord_6869480
  simp only [CollatzResearch.WordTrace]
  refine ⟨125275259576527324312394947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167033679435369765749859929 125275259576527324312394947)
  ·
    refine ⟨187912889364790986468592421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125275259576527324312394947 187912889364790986468592421)
    ·
      refine ⟨35233666755898309962861079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187912889364790986468592421 35233666755898309962861079)
      ·
        refine ⟨52850500133847464944291619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35233666755898309962861079 52850500133847464944291619)
        ·
          refine ⟨79275750200771197416437429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52850500133847464944291619 79275750200771197416437429)
          ·
            refine ⟨7432101581322299757791009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79275750200771197416437429 7432101581322299757791009)
            ·
              refine ⟨5574076185991724818343257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432101581322299757791009 5574076185991724818343257)
              ·
                refine ⟨4180557139493793613757443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574076185991724818343257 4180557139493793613757443)
                ·
                  refine ⟨6270835709240690420636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180557139493793613757443 6270835709240690420636165)
                  ·
                    refine ⟨1175781695482629453869281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6270835709240690420636165 1175781695482629453869281)
                    ·
                      rfl

theorem cell23_6869480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6869480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869480 prefixEnd_6869480 := by exact prefixLift 6869480
  have htrace : WordTrace (prefixWord ++ tailWord_6869480) baseStart_6869480 baseEnd_6869480 := by
    simpa [prefixWord, tailWord_6869480, baseEnd_6869480] using wordTrace_append hprefix tailTrace_6869480
  have hstable : (prefixWord ++ tailWord_6869480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869480).length < 2 ^ (prefixWord ++ tailWord_6869480).sum := by decide
  have hdescent : baseEnd_6869480 < baseStart_6869480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869509 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_6869509 : Nat := 118140960795 + 6869509 * 2 ^ 59
def prefixEnd_6869509 : Nat := 4983230072969 + 3 ^ 40 * 6869509 * 2
def baseEnd_6869509 : Nat := 3527359977386868748145209

theorem tailTrace_6869509 : CollatzResearch.WordTrace tailWord_6869509 prefixEnd_6869509 3527359977386868748145209 := by
  unfold tailWord_6869509
  simp only [CollatzResearch.WordTrace]
  refine ⟨250551576869949586577595581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167034384579966391051730387 250551576869949586577595581)
  ·
    refine ⟨93956841326231094966598343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250551576869949586577595581 93956841326231094966598343)
    ·
      refine ⟨140935261989346642449897515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93956841326231094966598343 140935261989346642449897515)
      ·
        refine ⟨211402892984019963674846273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140935261989346642449897515 211402892984019963674846273)
        ·
          refine ⟨158552169738014972756134705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211402892984019963674846273 158552169738014972756134705)
          ·
            refine ⟨118914127303511229567101029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158552169738014972756134705 118914127303511229567101029)
            ·
              refine ⟨22296398869408355543831443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118914127303511229567101029 22296398869408355543831443)
              ·
                refine ⟨33444598304112533315747165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22296398869408355543831443 33444598304112533315747165)
                ·
                  refine ⟨12541724364042199993405187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33444598304112533315747165 12541724364042199993405187)
                  ·
                    refine ⟨18812586546063299990107781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12541724364042199993405187 18812586546063299990107781)
                    ·
                      refine ⟨3527359977386868748145209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18812586546063299990107781 3527359977386868748145209)
                      ·
                        rfl

theorem cell23_6869509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_6869509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869509 prefixEnd_6869509 := by exact prefixLift 6869509
  have htrace : WordTrace (prefixWord ++ tailWord_6869509) baseStart_6869509 baseEnd_6869509 := by
    simpa [prefixWord, tailWord_6869509, baseEnd_6869509] using wordTrace_append hprefix tailTrace_6869509
  have hstable : (prefixWord ++ tailWord_6869509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869509).length < 2 ^ (prefixWord ++ tailWord_6869509).sum := by decide
  have hdescent : baseEnd_6869509 < baseStart_6869509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869546 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6869546 : Nat := 118140960795 + 6869546 * 2 ^ 59
def prefixEnd_6869546 : Nat := 4983230072969 + 3 ^ 40 * 6869546 * 2
def baseEnd_6869546 : Nat := 3527378976171085103382539

theorem tailTrace_6869546 : CollatzResearch.WordTrace tailWord_6869546 prefixEnd_6869546 3527378976171085103382539 := by
  unfold tailWord_6869546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62638231592703885474173123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167035284247210361264461661 62638231592703885474173123)
  ·
    refine ⟨93957347389055828211259685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62638231592703885474173123 93957347389055828211259685)
    ·
      refine ⟨17617002635447967789611191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93957347389055828211259685 17617002635447967789611191)
      ·
        refine ⟨26425503953171951684416787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17617002635447967789611191 26425503953171951684416787)
        ·
          refine ⟨39638255929757927526625181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26425503953171951684416787 39638255929757927526625181)
          ·
            refine ⟨14864345973659222822484443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39638255929757927526625181 14864345973659222822484443)
            ·
              refine ⟨22296518960488834233726665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14864345973659222822484443 22296518960488834233726665)
              ·
                refine ⟨16722389220366625675294999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22296518960488834233726665 16722389220366625675294999)
                ·
                  refine ⟨25083583830549938512942499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16722389220366625675294999 25083583830549938512942499)
                  ·
                    refine ⟨37625375745824907769413749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25083583830549938512942499 37625375745824907769413749)
                    ·
                      refine ⟨3527378976171085103382539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37625375745824907769413749 3527378976171085103382539)
                      ·
                        rfl

theorem cell23_6869546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6869546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869546 prefixEnd_6869546 := by exact prefixLift 6869546
  have htrace : WordTrace (prefixWord ++ tailWord_6869546) baseStart_6869546 baseEnd_6869546 := by
    simpa [prefixWord, tailWord_6869546, baseEnd_6869546] using wordTrace_append hprefix tailTrace_6869546
  have hstable : (prefixWord ++ tailWord_6869546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869546).length < 2 ^ (prefixWord ++ tailWord_6869546).sum := by decide
  have hdescent : baseEnd_6869546 < baseStart_6869546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869619 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3]
def baseStart_6869619 : Nat := 118140960795 + 6869619 * 2 ^ 59
def prefixEnd_6869619 : Nat := 4983230072969 + 3 ^ 40 * 6869619 * 2
def baseEnd_6869619 : Nat := 3527416460258863317769703

theorem tailTrace_6869619 : CollatzResearch.WordTrace tailWord_6869619 prefixEnd_6869619 3527416460258863317769703 := by
  unfold tailWord_6869619
  simp only [CollatzResearch.WordTrace]
  refine ⟨250555588899551075364099911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167037059266367383576066607 250555588899551075364099911)
  ·
    refine ⟨375833383349326613046149867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250555588899551075364099911 375833383349326613046149867)
    ·
      refine ⟨563750075023989919569224801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375833383349326613046149867 563750075023989919569224801)
      ·
        refine ⟨422812556267992439676918601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563750075023989919569224801 422812556267992439676918601)
        ·
          refine ⟨317109417200994329757688951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422812556267992439676918601 317109417200994329757688951)
          ·
            refine ⟨475664125801491494636533427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317109417200994329757688951 475664125801491494636533427)
            ·
              refine ⟨713496188702237241954800141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475664125801491494636533427 713496188702237241954800141)
              ·
                refine ⟨267561070763338965733050053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713496188702237241954800141 267561070763338965733050053)
                ·
                  refine ⟨50167700768126056074946885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267561070763338965733050053 50167700768126056074946885)
                  ·
                    refine ⟨9406443894023635514052541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50167700768126056074946885 9406443894023635514052541)
                    ·
                      refine ⟨3527416460258863317769703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9406443894023635514052541 3527416460258863317769703)
                      ·
                        rfl

theorem cell23_6869619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_6869619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869619 prefixEnd_6869619 := by exact prefixLift 6869619
  have htrace : WordTrace (prefixWord ++ tailWord_6869619) baseStart_6869619 baseEnd_6869619 := by
    simpa [prefixWord, tailWord_6869619, baseEnd_6869619] using wordTrace_append hprefix tailTrace_6869619
  have hstable : (prefixWord ++ tailWord_6869619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869619).length < 2 ^ (prefixWord ++ tailWord_6869619).sum := by decide
  have hdescent : baseEnd_6869619 < baseStart_6869619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869633 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6869633 : Nat := 118140960795 + 6869633 * 2 ^ 59
def prefixEnd_6869633 : Nat := 4983230072969 + 3 ^ 40 * 6869633 * 2
def baseEnd_6869633 : Nat := 3527423648988026262994639

theorem tailTrace_6869633 : CollatzResearch.WordTrace tailWord_6869633 prefixEnd_6869633 3527423648988026262994639 := by
  unfold tailWord_6869633
  simp only [CollatzResearch.WordTrace]
  refine ⟨250556099521500355755109553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167037399681000237170073035 250556099521500355755109553)
  ·
    refine ⟨187917074641125266816332165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250556099521500355755109553 187917074641125266816332165)
    ·
      refine ⟨35234451495210987528062281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187917074641125266816332165 35234451495210987528062281)
      ·
        refine ⟨26425838621408240646046711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35234451495210987528062281 26425838621408240646046711)
        ·
          refine ⟨39638757932112360969070067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26425838621408240646046711 39638757932112360969070067)
          ·
            refine ⟨59458136898168541453605101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39638757932112360969070067 59458136898168541453605101)
            ·
              refine ⟨22296801336813203045101913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59458136898168541453605101 22296801336813203045101913)
              ·
                refine ⟨16722601002609902283826435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22296801336813203045101913 16722601002609902283826435)
                ·
                  refine ⟨25083901503914853425739653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16722601002609902283826435 25083901503914853425739653)
                  ·
                    refine ⟨4703231531984035017326185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25083901503914853425739653 4703231531984035017326185)
                    ·
                      refine ⟨3527423648988026262994639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703231531984035017326185 3527423648988026262994639)
                      ·
                        rfl

theorem cell23_6869633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6869633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869633 prefixEnd_6869633 := by exact prefixLift 6869633
  have htrace : WordTrace (prefixWord ++ tailWord_6869633) baseStart_6869633 baseEnd_6869633 := by
    simpa [prefixWord, tailWord_6869633, baseEnd_6869633] using wordTrace_append hprefix tailTrace_6869633
  have hstable : (prefixWord ++ tailWord_6869633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869633).length < 2 ^ (prefixWord ++ tailWord_6869633).sum := by decide
  have hdescent : baseEnd_6869633 < baseStart_6869633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869636 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6869636 : Nat := 118140960795 + 6869636 * 2 ^ 59
def prefixEnd_6869636 : Nat := 4983230072969 + 3 ^ 40 * 6869636 * 2
def baseEnd_6869636 : Nat := 3527425189429989751257125

theorem tailTrace_6869636 : CollatzResearch.WordTrace tailWord_6869636 prefixEnd_6869636 3527425189429989751257125 := by
  unfold tailWord_6869636
  simp only [CollatzResearch.WordTrace]
  refine ⟨125278104470244743633734381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167037472626992991511645841 125278104470244743633734381)
  ·
    refine ⟨46979289176341778862650393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125278104470244743633734381 46979289176341778862650393)
    ·
      refine ⟨35234466882256334146987795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46979289176341778862650393 35234466882256334146987795)
      ·
        refine ⟨52851700323384501220481693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35234466882256334146987795 52851700323384501220481693)
        ·
          refine ⟨19819387621269187957680635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52851700323384501220481693 19819387621269187957680635)
          ·
            refine ⟨29729081431903781936520953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19819387621269187957680635 29729081431903781936520953)
            ·
              refine ⟨22296811073927836452390715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29729081431903781936520953 22296811073927836452390715)
              ·
                refine ⟨33445216610891754678586073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22296811073927836452390715 33445216610891754678586073)
                ·
                  refine ⟨25083912458168816008939555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33445216610891754678586073 25083912458168816008939555)
                  ·
                    refine ⟨37625868687253224013409333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25083912458168816008939555 37625868687253224013409333)
                    ·
                      refine ⟨3527425189429989751257125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37625868687253224013409333 3527425189429989751257125)
                      ·
                        rfl

theorem cell23_6869636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6869636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869636 prefixEnd_6869636 := by exact prefixLift 6869636
  have htrace : WordTrace (prefixWord ++ tailWord_6869636) baseStart_6869636 baseEnd_6869636 := by
    simpa [prefixWord, tailWord_6869636, baseEnd_6869636] using wordTrace_append hprefix tailTrace_6869636
  have hstable : (prefixWord ++ tailWord_6869636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869636).length < 2 ^ (prefixWord ++ tailWord_6869636).sum := by decide
  have hdescent : baseEnd_6869636 < baseStart_6869636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869646 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6869646 : Nat := 118140960795 + 6869646 * 2 ^ 59
def prefixEnd_6869646 : Nat := 4983230072969 + 3 ^ 40 * 6869646 * 2
def baseEnd_6869646 : Nat := 3527430324236534712132079

theorem tailTrace_6869646 : CollatzResearch.WordTrace tailWord_6869646 prefixEnd_6869646 3527430324236534712132079 := by
  unfold tailWord_6869646
  simp only [CollatzResearch.WordTrace]
  refine ⟨31319571708806657371916599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167037715780302172650221861 31319571708806657371916599)
  ·
    refine ⟨46979357563209986057874899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31319571708806657371916599 46979357563209986057874899)
    ·
      refine ⟨70469036344814979086812349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46979357563209986057874899 70469036344814979086812349)
      ·
        refine ⟨26425888629305617157554631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70469036344814979086812349 26425888629305617157554631)
        ·
          refine ⟨39638832943958425736331947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26425888629305617157554631 39638832943958425736331947)
          ·
            refine ⟨59458249415937638604497921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39638832943958425736331947 59458249415937638604497921)
            ·
              refine ⟨44593687061953228953373441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59458249415937638604497921 44593687061953228953373441)
              ·
                refine ⟨33445265296464921715030081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44593687061953228953373441 33445265296464921715030081)
                ·
                  refine ⟨25083948972348691286272561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33445265296464921715030081 25083948972348691286272561)
                  ·
                    refine ⟨18812961729261518464704421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25083948972348691286272561 18812961729261518464704421)
                    ·
                      refine ⟨3527430324236534712132079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18812961729261518464704421 3527430324236534712132079)
                      ·
                        rfl

theorem cell23_6869646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6869646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869646 prefixEnd_6869646 := by exact prefixLift 6869646
  have htrace : WordTrace (prefixWord ++ tailWord_6869646) baseStart_6869646 baseEnd_6869646 := by
    simpa [prefixWord, tailWord_6869646, baseEnd_6869646] using wordTrace_append hprefix tailTrace_6869646
  have hstable : (prefixWord ++ tailWord_6869646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869646).length < 2 ^ (prefixWord ++ tailWord_6869646).sum := by decide
  have hdescent : baseEnd_6869646 < baseStart_6869646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869669 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_6869669 : Nat := 118140960795 + 6869669 * 2 ^ 59
def prefixEnd_6869669 : Nat := 4983230072969 + 3 ^ 40 * 6869669 * 2
def baseEnd_6869669 : Nat := 1175814044763862707381491

theorem tailTrace_6869669 : CollatzResearch.WordTrace tailWord_6869669 prefixEnd_6869669 1175814044763862707381491 := by
  unfold tailWord_6869669
  simp only [CollatzResearch.WordTrace]
  refine ⟨250557412549369933903420061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167038275032913289268946707 250557412549369933903420061)
  ·
    refine ⟨93959029706013725213782523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250557412549369933903420061 93959029706013725213782523)
    ·
      refine ⟨140938544559020587820673785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93959029706013725213782523 140938544559020587820673785)
      ·
        refine ⟨105703908419265440865505339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140938544559020587820673785 105703908419265440865505339)
        ·
          refine ⟨158555862628898161298258009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105703908419265440865505339 158555862628898161298258009)
          ·
            refine ⟨118916896971673620973693507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158555862628898161298258009 118916896971673620973693507)
            ·
              refine ⟨178375345457510431460540261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118916896971673620973693507 178375345457510431460540261)
              ·
                refine ⟨33445377273283205898851299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178375345457510431460540261 33445377273283205898851299)
                ·
                  refine ⟨50168065909924808848276949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33445377273283205898851299 50168065909924808848276949)
                  ·
                    refine ⟨1175814044763862707381491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50168065909924808848276949 1175814044763862707381491)
                    ·
                      rfl

theorem cell23_6869669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_6869669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869669 prefixEnd_6869669 := by exact prefixLift 6869669
  have htrace : WordTrace (prefixWord ++ tailWord_6869669) baseStart_6869669 baseEnd_6869669 := by
    simpa [prefixWord, tailWord_6869669, baseEnd_6869669] using wordTrace_append hprefix tailTrace_6869669
  have hstable : (prefixWord ++ tailWord_6869669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869669).length < 2 ^ (prefixWord ++ tailWord_6869669).sum := by decide
  have hdescent : baseEnd_6869669 < baseStart_6869669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869733 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_6869733 : Nat := 118140960795 + 6869733 * 2 ^ 59
def prefixEnd_6869733 : Nat := 4983230072969 + 3 ^ 40 * 6869733 * 2
def baseEnd_6869733 : Nat := 1175824999017825290581393

theorem tailTrace_6869733 : CollatzResearch.WordTrace tailWord_6869733 prefixEnd_6869733 1175824999017825290581393 := by
  unfold tailWord_6869733
  simp only [CollatzResearch.WordTrace]
  refine ⟨250559746821138072833749853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167039831214092048555833235 250559746821138072833749853)
  ·
    refine ⟨93959905057926777312656195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250559746821138072833749853 93959905057926777312656195)
    ·
      refine ⟨140939857586890165968984293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93959905057926777312656195 140939857586890165968984293)
      ·
        refine ⟨26426223297541906119184555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140939857586890165968984293 26426223297541906119184555)
        ·
          refine ⟨39639334946312859178776833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26426223297541906119184555 39639334946312859178776833)
          ·
            refine ⟨29729501209734644384082625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39639334946312859178776833 29729501209734644384082625)
            ·
              refine ⟨22297125907300983288061969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29729501209734644384082625 22297125907300983288061969)
              ·
                refine ⟨16722844430475737466046477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22297125907300983288061969 16722844430475737466046477)
                ·
                  refine ⟨6271066661428401549767429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16722844430475737466046477 6271066661428401549767429)
                  ·
                    refine ⟨1175824999017825290581393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271066661428401549767429 1175824999017825290581393)
                    ·
                      rfl

theorem cell23_6869733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_6869733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869733 prefixEnd_6869733 := by exact prefixLift 6869733
  have htrace : WordTrace (prefixWord ++ tailWord_6869733) baseStart_6869733 baseEnd_6869733 := by
    simpa [prefixWord, tailWord_6869733, baseEnd_6869733] using wordTrace_append hprefix tailTrace_6869733
  have hstable : (prefixWord ++ tailWord_6869733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869733).length < 2 ^ (prefixWord ++ tailWord_6869733).sum := by decide
  have hdescent : baseEnd_6869733 < baseStart_6869733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869746 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_6869746 : Nat := 118140960795 + 6869746 * 2 ^ 59
def prefixEnd_6869746 : Nat := 4983230072969 + 3 ^ 40 * 6869746 * 2
def baseEnd_6869746 : Nat := 391942408033553813431291

theorem tailTrace_6869746 : CollatzResearch.WordTrace tailWord_6869746 prefixEnd_6869746 391942408033553813431291 := by
  unfold tailWord_6869746
  simp only [CollatzResearch.WordTrace]
  refine ⟨62640055242522744013493273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167040147313393984035982061 62640055242522744013493273)
  ·
    refine ⟨46980041431892058010119955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62640055242522744013493273 46980041431892058010119955)
    ·
      refine ⟨70470062147838087015179933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46980041431892058010119955 70470062147838087015179933)
      ·
        refine ⟨26426273305439282630692475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70470062147838087015179933 26426273305439282630692475)
        ·
          refine ⟨39639409958158923946038713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26426273305439282630692475 39639409958158923946038713)
          ·
            refine ⟨29729557468619192959529035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39639409958158923946038713 29729557468619192959529035)
            ·
              refine ⟨44594336202928789439293553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29729557468619192959529035 44594336202928789439293553)
              ·
                refine ⟨33445752152196592079470165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44594336202928789439293553 33445752152196592079470165)
                ·
                  refine ⟨391942408033553813431291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33445752152196592079470165 391942408033553813431291)
                  ·
                    rfl

theorem cell23_6869746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_6869746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869746 prefixEnd_6869746 := by exact prefixLift 6869746
  have htrace : WordTrace (prefixWord ++ tailWord_6869746) baseStart_6869746 baseEnd_6869746 := by
    simpa [prefixWord, tailWord_6869746, baseEnd_6869746] using wordTrace_append hprefix tailTrace_6869746
  have hstable : (prefixWord ++ tailWord_6869746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869746).length < 2 ^ (prefixWord ++ tailWord_6869746).sum := by decide
  have hdescent : baseEnd_6869746 < baseStart_6869746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869810 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_6869810 : Nat := 118140960795 + 6869810 * 2 ^ 59
def prefixEnd_6869810 : Nat := 4983230072969 + 3 ^ 40 * 6869810 * 2
def baseEnd_6869810 : Nat := 1175838178354624023493775

theorem tailTrace_6869810 : CollatzResearch.WordTrace tailWord_6869810 prefixEnd_6869810 1175838178354624023493775 := by
  unfold tailWord_6869810
  simp only [CollatzResearch.WordTrace]
  refine ⟨62640638810464778746075721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167041703494572743322868589 62640638810464778746075721)
  ·
    refine ⟨46980479107848584059556791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62640638810464778746075721 46980479107848584059556791)
    ·
      refine ⟨70470718661772876089335187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46980479107848584059556791 70470718661772876089335187)
      ·
        refine ⟨105706077992659314134002781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70470718661772876089335187 105706077992659314134002781)
        ·
          refine ⟨39639779247247242800251043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105706077992659314134002781 39639779247247242800251043)
          ·
            refine ⟨59459668870870864200376565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39639779247247242800251043 59459668870870864200376565)
            ·
              refine ⟨5574343956644143518785303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59459668870870864200376565 5574343956644143518785303)
              ·
                refine ⟨8361515934966215278177955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5574343956644143518785303 8361515934966215278177955)
                ·
                  refine ⟨12542273902449322917266933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8361515934966215278177955 12542273902449322917266933)
                  ·
                    refine ⟨1175838178354624023493775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12542273902449322917266933 1175838178354624023493775)
                    ·
                      rfl

theorem cell23_6869810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_6869810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869810 prefixEnd_6869810 := by exact prefixLift 6869810
  have htrace : WordTrace (prefixWord ++ tailWord_6869810) baseStart_6869810 baseEnd_6869810 := by
    simpa [prefixWord, tailWord_6869810, baseEnd_6869810] using wordTrace_append hprefix tailTrace_6869810
  have hstable : (prefixWord ++ tailWord_6869810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869810).length < 2 ^ (prefixWord ++ tailWord_6869810).sum := by decide
  have hdescent : baseEnd_6869810 < baseStart_6869810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869833 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_6869833 : Nat := 118140960795 + 6869833 * 2 ^ 59
def prefixEnd_6869833 : Nat := 4983230072969 + 3 ^ 40 * 6869833 * 2
def baseEnd_6869833 : Nat := 3527526345118925480493719

theorem tailTrace_6869833 : CollatzResearch.WordTrace tailWord_6869833 prefixEnd_6869833 3527526345118925480493719 := by
  unfold tailWord_6869833
  simp only [CollatzResearch.WordTrace]
  refine ⟨250563394120775789912390153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167042262747183859941593435 250563394120775789912390153)
  ·
    refine ⟨187922545590581842434292615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250563394120775789912390153 187922545590581842434292615)
    ·
      refine ⟨281883818385872763651438923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187922545590581842434292615 281883818385872763651438923)
      ·
        refine ⟨422825727578809145477158385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281883818385872763651438923 422825727578809145477158385)
        ·
          refine ⟨317119295684106859107868789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422825727578809145477158385 317119295684106859107868789)
          ·
            refine ⟨29729933970385018041362699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317119295684106859107868789 29729933970385018041362699)
            ·
              refine ⟨44594900955577527062044049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29729933970385018041362699 44594900955577527062044049)
              ·
                refine ⟨33446175716683145296533037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44594900955577527062044049 33446175716683145296533037)
                ·
                  refine ⟨12542315893756179486199889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33446175716683145296533037 12542315893756179486199889)
                  ·
                    refine ⟨9406736920317134614649917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12542315893756179486199889 9406736920317134614649917)
                    ·
                      refine ⟨3527526345118925480493719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9406736920317134614649917 3527526345118925480493719)
                      ·
                        rfl

theorem cell23_6869833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_6869833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869833 prefixEnd_6869833 := by exact prefixLift 6869833
  have htrace : WordTrace (prefixWord ++ tailWord_6869833) baseStart_6869833 baseEnd_6869833 := by
    simpa [prefixWord, tailWord_6869833, baseEnd_6869833] using wordTrace_append hprefix tailTrace_6869833
  have hstable : (prefixWord ++ tailWord_6869833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869833).length < 2 ^ (prefixWord ++ tailWord_6869833).sum := by decide
  have hdescent : baseEnd_6869833 < baseStart_6869833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869847 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_6869847 : Nat := 118140960795 + 6869847 * 2 ^ 59
def prefixEnd_6869847 : Nat := 4983230072969 + 3 ^ 40 * 6869847 * 2
def baseEnd_6869847 : Nat := 3527533533848088425718655

theorem tailTrace_6869847 : CollatzResearch.WordTrace tailWord_6869847 prefixEnd_6869847 3527533533848088425718655 := by
  unfold tailWord_6869847
  simp only [CollatzResearch.WordTrace]
  refine ⟨250563904742725070303399795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167042603161816713535599863 250563904742725070303399795)
  ·
    refine ⟨375845857114087605455099693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250563904742725070303399795 375845857114087605455099693)
    ·
      refine ⟨140942196417782852045662385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375845857114087605455099693 140942196417782852045662385)
      ·
        refine ⟨105706647313337139034246789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140942196417782852045662385 105706647313337139034246789)
        ·
          refine ⟨19819996371250713568921273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105706647313337139034246789 19819996371250713568921273)
          ·
            refine ⟨14864997278438035176690955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19819996371250713568921273 14864997278438035176690955)
            ·
              refine ⟨22297495917657052765036433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14864997278438035176690955 22297495917657052765036433)
              ·
                refine ⟨16723121938242789573777325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22297495917657052765036433 16723121938242789573777325)
                ·
                  refine ⟨6271170726841046090166497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16723121938242789573777325 6271170726841046090166497)
                  ·
                    refine ⟨4703378045130784567624873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271170726841046090166497 4703378045130784567624873)
                    ·
                      refine ⟨3527533533848088425718655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703378045130784567624873 3527533533848088425718655)
                      ·
                        rfl

theorem cell23_6869847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_6869847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869847 prefixEnd_6869847 := by exact prefixLift 6869847
  have htrace : WordTrace (prefixWord ++ tailWord_6869847) baseStart_6869847 baseEnd_6869847 := by
    simpa [prefixWord, tailWord_6869847, baseEnd_6869847] using wordTrace_append hprefix tailTrace_6869847
  have hstable : (prefixWord ++ tailWord_6869847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869847).length < 2 ^ (prefixWord ++ tailWord_6869847).sum := by decide
  have hdescent : baseEnd_6869847 < baseStart_6869847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869864 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6869864 : Nat := 118140960795 + 6869864 * 2 ^ 59
def prefixEnd_6869864 : Nat := 4983230072969 + 3 ^ 40 * 6869864 * 2
def baseEnd_6869864 : Nat := 3527542263019214859206077

theorem tailTrace_6869864 : CollatzResearch.WordTrace tailWord_6869864 prefixEnd_6869864 3527542263019214859206077 := by
  unfold tailWord_6869864
  simp only [CollatzResearch.WordTrace]
  refine ⟨125282262391831741103384323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167043016522442321471179097 125282262391831741103384323)
  ·
    refine ⟨187923393587747611655076485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125282262391831741103384323 187923393587747611655076485)
    ·
      refine ⟨35235636297702677185326841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187923393587747611655076485 35235636297702677185326841)
      ·
        refine ⟨26426727223277007888995131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35235636297702677185326841 26426727223277007888995131)
        ·
          refine ⟨39640090834915511833492697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26426727223277007888995131 39640090834915511833492697)
          ·
            refine ⟨29730068126186633875119523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39640090834915511833492697 29730068126186633875119523)
            ·
              refine ⟨44595102189279950812679285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29730068126186633875119523 44595102189279950812679285)
              ·
                refine ⟨4180790830244995388688683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44595102189279950812679285 4180790830244995388688683)
                ·
                  refine ⟨6271186245367493083033025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180790830244995388688683 6271186245367493083033025)
                  ·
                    refine ⟨4703389684025619812274769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271186245367493083033025 4703389684025619812274769)
                    ·
                      refine ⟨3527542263019214859206077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703389684025619812274769 3527542263019214859206077)
                      ·
                        rfl

theorem cell23_6869864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6869864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869864 prefixEnd_6869864 := by exact prefixLift 6869864
  have htrace : WordTrace (prefixWord ++ tailWord_6869864) baseStart_6869864 baseEnd_6869864 := by
    simpa [prefixWord, tailWord_6869864, baseEnd_6869864] using wordTrace_append hprefix tailTrace_6869864
  have hstable : (prefixWord ++ tailWord_6869864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869864).length < 2 ^ (prefixWord ++ tailWord_6869864).sum := by decide
  have hdescent : baseEnd_6869864 < baseStart_6869864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869880 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_6869880 : Nat := 118140960795 + 6869880 * 2 ^ 59
def prefixEnd_6869880 : Nat := 4983230072969 + 3 ^ 40 * 6869880 * 2
def baseEnd_6869880 : Nat := 3527550478709686796606003

theorem tailTrace_6869880 : CollatzResearch.WordTrace tailWord_6869880 prefixEnd_6869880 3527550478709686796606003 := by
  unfold tailWord_6869880
  simp only [CollatzResearch.WordTrace]
  refine ⟨125282554175802758469675547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167043405567737011292900729 125282554175802758469675547)
  ·
    refine ⟨187923831263704137704513321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125282554175802758469675547 187923831263704137704513321)
    ·
      refine ⟨140942873447778103278384991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187923831263704137704513321 140942873447778103278384991)
      ·
        refine ⟨211414310171667154917577487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140942873447778103278384991 211414310171667154917577487)
        ·
          refine ⟨317121465257500732376366231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211414310171667154917577487 317121465257500732376366231)
          ·
            refine ⟨475682197886251098564549347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317121465257500732376366231 475682197886251098564549347)
            ·
              refine ⟨713523296829376647846824021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475682197886251098564549347 713523296829376647846824021)
              ·
                refine ⟨8361601134719257591954969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 713523296829376647846824021 8361601134719257591954969)
                ·
                  refine ⟨6271200851039443193966227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8361601134719257591954969 6271200851039443193966227)
                  ·
                    refine ⟨9406801276559164790949341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6271200851039443193966227 9406801276559164790949341)
                    ·
                      refine ⟨3527550478709686796606003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9406801276559164790949341 3527550478709686796606003)
                      ·
                        rfl

theorem cell23_6869880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_6869880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869880 prefixEnd_6869880 := by exact prefixLift 6869880
  have htrace : WordTrace (prefixWord ++ tailWord_6869880) baseStart_6869880 baseEnd_6869880 := by
    simpa [prefixWord, tailWord_6869880, baseEnd_6869880] using wordTrace_append hprefix tailTrace_6869880
  have hstable : (prefixWord ++ tailWord_6869880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869880).length < 2 ^ (prefixWord ++ tailWord_6869880).sum := by decide
  have hdescent : baseEnd_6869880 < baseStart_6869880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869920 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2]
def baseStart_6869920 : Nat := 118140960795 + 6869920 * 2 ^ 59
def prefixEnd_6869920 : Nat := 4983230072969 + 3 ^ 40 * 6869920 * 2
def baseEnd_6869920 : Nat := 3527571017935866640105819

theorem tailTrace_6869920 : CollatzResearch.WordTrace tailWord_6869920 prefixEnd_6869920 3527571017935866640105819 := by
  unfold tailWord_6869920
  simp only [CollatzResearch.WordTrace]
  refine ⟨125283283635730301885403607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167044378180973735847204809 125283283635730301885403607)
  ·
    refine ⟨187924925453595452828105411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125283283635730301885403607 187924925453595452828105411)
    ·
      refine ⟨281887388180393179242158117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187924925453595452828105411 281887388180393179242158117)
      ·
        refine ⟨52853885283823721107904647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281887388180393179242158117 52853885283823721107904647)
        ·
          refine ⟨79280827925735581661856971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52853885283823721107904647 79280827925735581661856971)
          ·
            refine ⟨118921241888603372492785457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79280827925735581661856971 118921241888603372492785457)
            ·
              refine ⟨89190931416452529369589093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118921241888603372492785457 89190931416452529369589093)
              ·
                refine ⟨16723299640584849256797955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89190931416452529369589093 16723299640584849256797955)
                ·
                  refine ⟨25084949460877273885196933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16723299640584849256797955 25084949460877273885196933)
                  ·
                    refine ⟨4703428023914488853474425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25084949460877273885196933 4703428023914488853474425)
                    ·
                      refine ⟨3527571017935866640105819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703428023914488853474425 3527571017935866640105819)
                      ·
                        rfl

theorem cell23_6869920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_6869920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869920 prefixEnd_6869920 := by exact prefixLift 6869920
  have htrace : WordTrace (prefixWord ++ tailWord_6869920) baseStart_6869920 baseEnd_6869920 := by
    simpa [prefixWord, tailWord_6869920, baseEnd_6869920] using wordTrace_append hprefix tailTrace_6869920
  have hstable : (prefixWord ++ tailWord_6869920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869920).length < 2 ^ (prefixWord ++ tailWord_6869920).sum := by decide
  have hdescent : baseEnd_6869920 < baseStart_6869920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869943 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 7]
def baseStart_6869943 : Nat := 118140960795 + 6869943 * 2 ^ 59
def prefixEnd_6869943 : Nat := 4983230072969 + 3 ^ 40 * 6869943 * 2
def baseEnd_6869943 : Nat := 391953647554546672235357

theorem tailTrace_6869943 : CollatzResearch.WordTrace tailWord_6869943 prefixEnd_6869943 391953647554546672235357 := by
  unfold tailWord_6869943
  simp only [CollatzResearch.WordTrace]
  refine ⟨250567406150377278698894483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167044937433584852465929655 250567406150377278698894483)
  ·
    refine ⟨375851109225565918048341725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250567406150377278698894483 375851109225565918048341725)
    ·
      refine ⟨140944165959587219268128147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375851109225565918048341725 140944165959587219268128147)
      ·
        refine ⟨211416248939380828902192221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140944165959587219268128147 211416248939380828902192221)
        ·
          refine ⟨79281093352267810838322083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211416248939380828902192221 79281093352267810838322083)
          ·
            refine ⟨118921640028401716257483125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79281093352267810838322083 118921640028401716257483125)
            ·
              refine ⟨11148903752662660899139043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118921640028401716257483125 11148903752662660899139043)
              ·
                refine ⟨16723355628993991348708565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11148903752662660899139043 16723355628993991348708565)
                ·
                  refine ⟨391953647554546672235357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16723355628993991348708565 391953647554546672235357)
                  ·
                    rfl

theorem cell23_6869943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 7].length) (baseStart_6869943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869943 prefixEnd_6869943 := by exact prefixLift 6869943
  have htrace : WordTrace (prefixWord ++ tailWord_6869943) baseStart_6869943 baseEnd_6869943 := by
    simpa [prefixWord, tailWord_6869943, baseEnd_6869943] using wordTrace_append hprefix tailTrace_6869943
  have hstable : (prefixWord ++ tailWord_6869943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869943).length < 2 ^ (prefixWord ++ tailWord_6869943).sum := by decide
  have hdescent : baseEnd_6869943 < baseStart_6869943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6869994 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_6869994 : Nat := 118140960795 + 6869994 * 2 ^ 59
def prefixEnd_6869994 : Nat := 4983230072969 + 3 ^ 40 * 6869994 * 2
def baseEnd_6869994 : Nat := 391956557278255483397831

theorem tailTrace_6869994 : CollatzResearch.WordTrace tailWord_6869994 prefixEnd_6869994 391956557278255483397831 := by
  unfold tailWord_6869994
  simp only [CollatzResearch.WordTrace]
  refine ⟨62642316568298128602250259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167046177515461676272667357 62642316568298128602250259)
  ·
    refine ⟨93963474852447192903375389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62642316568298128602250259 93963474852447192903375389)
    ·
      refine ⟨35236303069667697338765771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93963474852447192903375389 35236303069667697338765771)
      ·
        refine ⟨52854454604501546008148657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35236303069667697338765771 52854454604501546008148657)
        ·
          refine ⟨39640840953376159506111493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52854454604501546008148657 39640840953376159506111493)
          ·
            refine ⟨7432657678758029907395905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39640840953376159506111493 7432657678758029907395905)
            ·
              refine ⟨5574493259068522430546929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432657678758029907395905 5574493259068522430546929)
              ·
                refine ⟨4180869944301391822910197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574493259068522430546929 4180869944301391822910197)
                ·
                  refine ⟨391956557278255483397831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4180869944301391822910197 391956557278255483397831)
                  ·
                    rfl

theorem cell23_6869994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_6869994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6869994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6869994 prefixEnd_6869994 := by exact prefixLift 6869994
  have htrace : WordTrace (prefixWord ++ tailWord_6869994) baseStart_6869994 baseEnd_6869994 := by
    simpa [prefixWord, tailWord_6869994, baseEnd_6869994] using wordTrace_append hprefix tailTrace_6869994
  have hstable : (prefixWord ++ tailWord_6869994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6869994).length < 2 ^ (prefixWord ++ tailWord_6869994).sum := by decide
  have hdescent : baseEnd_6869994 < baseStart_6869994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6869994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870027 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 4]
def baseStart_6870027 : Nat := 118140960795 + 6870027 * 2 ^ 59
def prefixEnd_6870027 : Nat := 4983230072969 + 3 ^ 40 * 6870027 * 2
def baseEnd_6870027 : Nat := 3527625960365897721467827

theorem tailTrace_6870027 : CollatzResearch.WordTrace tailWord_6870027 prefixEnd_6870027 3527625960365897721467827 := by
  unfold tailWord_6870027
  simp only [CollatzResearch.WordTrace]
  refine ⟨250570469882072961044952335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167046979921381974029968223 250570469882072961044952335)
  ·
    refine ⟨375855704823109441567428503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250570469882072961044952335 375855704823109441567428503)
    ·
      refine ⟨563783557234664162351142755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375855704823109441567428503 563783557234664162351142755)
      ·
        refine ⟨845675335851996243526714133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563783557234664162351142755 845675335851996243526714133)
        ·
          refine ⟨39641031368062323915314725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 845675335851996243526714133 39641031368062323915314725)
          ·
            refine ⟨7432693381511685734121511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39641031368062323915314725 7432693381511685734121511)
            ·
              refine ⟨11149040072267528601182267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432693381511685734121511 11149040072267528601182267)
              ·
                refine ⟨16723560108401292901773401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11149040072267528601182267 16723560108401292901773401)
                ·
                  refine ⟨12542670081300969676330051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16723560108401292901773401 12542670081300969676330051)
                  ·
                    refine ⟨18814005121951454514495077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12542670081300969676330051 18814005121951454514495077)
                    ·
                      refine ⟨3527625960365897721467827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18814005121951454514495077 3527625960365897721467827)
                      ·
                        rfl

theorem cell23_6870027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 4].length) (baseStart_6870027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870027 prefixEnd_6870027 := by exact prefixLift 6870027
  have htrace : WordTrace (prefixWord ++ tailWord_6870027) baseStart_6870027 baseEnd_6870027 := by
    simpa [prefixWord, tailWord_6870027, baseEnd_6870027] using wordTrace_append hprefix tailTrace_6870027
  have hstable : (prefixWord ++ tailWord_6870027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870027).length < 2 ^ (prefixWord ++ tailWord_6870027).sum := by decide
  have hdescent : baseEnd_6870027 < baseStart_6870027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870050 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_6870050 : Nat := 118140960795 + 6870050 * 2 ^ 59
def prefixEnd_6870050 : Nat := 4983230072969 + 3 ^ 40 * 6870050 * 2
def baseEnd_6870050 : Nat := 391959752268994570164469

theorem tailTrace_6870050 : CollatzResearch.WordTrace tailWord_6870050 prefixEnd_6870050 391959752268994570164469 := by
  unfold tailWord_6870050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62642827190247408993259901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167047539173993090648693069 62642827190247408993259901)
  ·
    refine ⟨23491060196342778372472463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62642827190247408993259901 23491060196342778372472463)
    ·
      refine ⟨35236590294514167558708695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23491060196342778372472463 35236590294514167558708695)
      ·
        refine ⟨52854885441771251338063043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35236590294514167558708695 52854885441771251338063043)
        ·
          refine ⟨79282328162656877007094565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52854885441771251338063043 79282328162656877007094565)
          ·
            refine ⟨14865436530498164438830231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79282328162656877007094565 14865436530498164438830231)
            ·
              refine ⟨22298154795747246658245347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14865436530498164438830231 22298154795747246658245347)
              ·
                refine ⟨33447232193620869987368021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22298154795747246658245347 33447232193620869987368021)
                ·
                  refine ⟨391959752268994570164469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33447232193620869987368021 391959752268994570164469)
                  ·
                    rfl

theorem cell23_6870050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_6870050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870050 prefixEnd_6870050 := by exact prefixLift 6870050
  have htrace : WordTrace (prefixWord ++ tailWord_6870050) baseStart_6870050 baseEnd_6870050 := by
    simpa [prefixWord, tailWord_6870050, baseEnd_6870050] using wordTrace_append hprefix tailTrace_6870050
  have hstable : (prefixWord ++ tailWord_6870050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870050).length < 2 ^ (prefixWord ++ tailWord_6870050).sum := by decide
  have hdescent : baseEnd_6870050 < baseStart_6870050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870053 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_6870053 : Nat := 118140960795 + 6870053 * 2 ^ 59
def prefixEnd_6870053 : Nat := 4983230072969 + 3 ^ 40 * 6870053 * 2
def baseEnd_6870053 : Nat := 3527639310862914619742707

theorem tailTrace_6870053 : CollatzResearch.WordTrace tailWord_6870053 prefixEnd_6870053 3527639310862914619742707 := by
  unfold tailWord_6870053
  simp only [CollatzResearch.WordTrace]
  refine ⟨250571418179978767485398813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167047612119985844990265875 250571418179978767485398813)
  ·
    refine ⟨93964281817492037807024555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250571418179978767485398813 93964281817492037807024555)
    ·
      refine ⟨140946422726238056710536833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93964281817492037807024555 140946422726238056710536833)
      ·
        refine ⟨105709817044678542532902625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140946422726238056710536833 105709817044678542532902625)
        ·
          refine ⟨79282362783508906899676969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105709817044678542532902625 79282362783508906899676969)
          ·
            refine ⟨59461772087631680174757727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79282362783508906899676969 59461772087631680174757727)
            ·
              refine ⟨89192658131447520262136591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59461772087631680174757727 89192658131447520262136591)
              ·
                refine ⟨133788987197171280393204887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89192658131447520262136591 133788987197171280393204887)
                ·
                  refine ⟨200683480795756920589807331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133788987197171280393204887 200683480795756920589807331)
                  ·
                    refine ⟨301025221193635380884710997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200683480795756920589807331 301025221193635380884710997)
                    ·
                      refine ⟨3527639310862914619742707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 301025221193635380884710997 3527639310862914619742707)
                      ·
                        rfl

theorem cell23_6870053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_6870053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870053 prefixEnd_6870053 := by exact prefixLift 6870053
  have htrace : WordTrace (prefixWord ++ tailWord_6870053) baseStart_6870053 baseEnd_6870053 := by
    simpa [prefixWord, tailWord_6870053, baseEnd_6870053] using wordTrace_append hprefix tailTrace_6870053
  have hstable : (prefixWord ++ tailWord_6870053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870053).length < 2 ^ (prefixWord ++ tailWord_6870053).sum := by decide
  have hdescent : baseEnd_6870053 < baseStart_6870053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870087 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_6870087 : Nat := 118140960795 + 6870087 * 2 ^ 59
def prefixEnd_6870087 : Nat := 4983230072969 + 3 ^ 40 * 6870087 * 2
def baseEnd_6870087 : Nat := 3527656769205167486717551

theorem tailTrace_6870087 : CollatzResearch.WordTrace tailWord_6870087 prefixEnd_6870087 3527656769205167486717551 := by
  unfold tailWord_6870087
  simp only [CollatzResearch.WordTrace]
  refine ⟨250572658261855591292136515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167048438841237060861424343 250572658261855591292136515)
  ·
    refine ⟨375858987392783386938204773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250572658261855591292136515 375858987392783386938204773)
    ·
      refine ⟨70473560136146885050913395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375858987392783386938204773 70473560136146885050913395)
      ·
        refine ⟨105710340204220327576370093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70473560136146885050913395 105710340204220327576370093)
        ·
          refine ⟨39641377576582622841138785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105710340204220327576370093 39641377576582622841138785)
          ·
            refine ⟨29731033182436967130854089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39641377576582622841138785 29731033182436967130854089)
            ·
              refine ⟨22298274886827725348140567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29731033182436967130854089 22298274886827725348140567)
              ·
                refine ⟨33447412330241588022210851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22298274886827725348140567 33447412330241588022210851)
                ·
                  refine ⟨50171118495362382033316277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33447412330241588022210851 50171118495362382033316277)
                  ·
                    refine ⟨4703542358940223315623401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50171118495362382033316277 4703542358940223315623401)
                    ·
                      refine ⟨3527656769205167486717551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703542358940223315623401 3527656769205167486717551)
                      ·
                        rfl

theorem cell23_6870087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_6870087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870087 prefixEnd_6870087 := by exact prefixLift 6870087
  have htrace : WordTrace (prefixWord ++ tailWord_6870087) baseStart_6870087 baseEnd_6870087 := by
    simpa [prefixWord, tailWord_6870087, baseEnd_6870087] using wordTrace_append hprefix tailTrace_6870087
  have hstable : (prefixWord ++ tailWord_6870087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870087).length < 2 ^ (prefixWord ++ tailWord_6870087).sum := by decide
  have hdescent : baseEnd_6870087 < baseStart_6870087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870111 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 1, 1, 3]
def baseStart_6870111 : Nat := 118140960795 + 6870111 * 2 ^ 59
def prefixEnd_6870111 : Nat := 4983230072969 + 3 ^ 40 * 6870111 * 2
def baseEnd_6870111 : Nat := 3527669092740875392817441

theorem tailTrace_6870111 : CollatzResearch.WordTrace tailWord_6870111 prefixEnd_6870111 3527669092740875392817441 := by
  unfold tailWord_6870111
  simp only [CollatzResearch.WordTrace]
  refine ⟨250573533613768643391010187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167049022409179095594006791 250573533613768643391010187)
  ·
    refine ⟨375860300420652965086515281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250573533613768643391010187 375860300420652965086515281)
    ·
      refine ⟨281895225315489723814886461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375860300420652965086515281 281895225315489723814886461)
      ·
        refine ⟨105710709493308646430582423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281895225315489723814886461 105710709493308646430582423)
        ·
          refine ⟨158566064239962969645873635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105710709493308646430582423 158566064239962969645873635)
          ·
            refine ⟨237849096359944454468810453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158566064239962969645873635 237849096359944454468810453)
            ·
              refine ⟨5574588195936198151612745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237849096359944454468810453 5574588195936198151612745)
              ·
                refine ⟨4180941146952148613709559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574588195936198151612745 4180941146952148613709559)
                ·
                  refine ⟨6271411720428222920564339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180941146952148613709559 6271411720428222920564339)
                  ·
                    refine ⟨9407117580642334380846509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6271411720428222920564339 9407117580642334380846509)
                    ·
                      refine ⟨3527669092740875392817441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9407117580642334380846509 3527669092740875392817441)
                      ·
                        rfl

theorem cell23_6870111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_6870111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870111 prefixEnd_6870111 := by exact prefixLift 6870111
  have htrace : WordTrace (prefixWord ++ tailWord_6870111) baseStart_6870111 baseEnd_6870111 := by
    simpa [prefixWord, tailWord_6870111, baseEnd_6870111] using wordTrace_append hprefix tailTrace_6870111
  have hstable : (prefixWord ++ tailWord_6870111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870111).length < 2 ^ (prefixWord ++ tailWord_6870111).sum := by decide
  have hdescent : baseEnd_6870111 < baseStart_6870111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870127 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 2, 4]
def baseStart_6870127 : Nat := 118140960795 + 6870127 * 2 ^ 59
def prefixEnd_6870127 : Nat := 4983230072969 + 3 ^ 40 * 6870127 * 2
def baseEnd_6870127 : Nat := 1175892436143782443405789

theorem tailTrace_6870127 : CollatzResearch.WordTrace tailWord_6870127 prefixEnd_6870127 1175892436143782443405789 := by
  unfold tailWord_6870127
  simp only [CollatzResearch.WordTrace]
  refine ⟨250574117181710678123592635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167049411454473785415728423 250574117181710678123592635)
  ·
    refine ⟨375861175772566017185388953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250574117181710678123592635 375861175772566017185388953)
    ·
      refine ⟨281895881829424512889041715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375861175772566017185388953 281895881829424512889041715)
      ·
        refine ⟨422843822744136769333562573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281895881829424512889041715 422843822744136769333562573)
        ·
          refine ⟨158566433529051288500085965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422843822744136769333562573 158566433529051288500085965)
          ·
            refine ⟨59462412573394233187532237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158566433529051288500085965 59462412573394233187532237)
            ·
              refine ⟨22298404715022837445324589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59462412573394233187532237 22298404715022837445324589)
              ·
                refine ⟨8361901768133564041996721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22298404715022837445324589 8361901768133564041996721)
                ·
                  refine ⟨6271426326100173031497541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8361901768133564041996721 6271426326100173031497541)
                  ·
                    refine ⟨1175892436143782443405789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271426326100173031497541 1175892436143782443405789)
                    ·
                      rfl

theorem cell23_6870127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_6870127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870127 prefixEnd_6870127 := by exact prefixLift 6870127
  have htrace : WordTrace (prefixWord ++ tailWord_6870127) baseStart_6870127 baseEnd_6870127 := by
    simpa [prefixWord, tailWord_6870127, baseEnd_6870127] using wordTrace_append hprefix tailTrace_6870127
  have hstable : (prefixWord ++ tailWord_6870127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870127).length < 2 ^ (prefixWord ++ tailWord_6870127).sum := by decide
  have hdescent : baseEnd_6870127 < baseStart_6870127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870130 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_6870130 : Nat := 118140960795 + 6870130 * 2 ^ 59
def prefixEnd_6870130 : Nat := 4983230072969 + 3 ^ 40 * 6870130 * 2
def baseEnd_6870130 : Nat := 3527678848873310818479853

theorem tailTrace_6870130 : CollatzResearch.WordTrace tailWord_6870130 prefixEnd_6870130 3527678848873310818479853 := by
  unfold tailWord_6870130
  simp only [CollatzResearch.WordTrace]
  refine ⟨62643556650174952408987961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167049484400466539757301229 62643556650174952408987961)
  ·
    refine ⟨46982667487631214306740971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62643556650174952408987961 46982667487631214306740971)
    ·
      refine ⟨70474001231446821460111457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46982667487631214306740971 70474001231446821460111457)
      ·
        refine ⟨52855500923585116095083593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70474001231446821460111457 52855500923585116095083593)
        ·
          refine ⟨39641625692688837071312695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52855500923585116095083593 39641625692688837071312695)
          ·
            refine ⟨59462438539033255606969043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39641625692688837071312695 59462438539033255606969043)
            ·
              refine ⟨89193657808549883410453565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59462438539033255606969043 89193657808549883410453565)
              ·
                refine ⟨33447621678206206278920087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89193657808549883410453565 33447621678206206278920087)
                ·
                  refine ⟨50171432517309309418380131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33447621678206206278920087 50171432517309309418380131)
                  ·
                    refine ⟨75257148775963964127570197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50171432517309309418380131 75257148775963964127570197)
                    ·
                      refine ⟨3527678848873310818479853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75257148775963964127570197 3527678848873310818479853)
                      ·
                        rfl

theorem cell23_6870130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_6870130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870130 prefixEnd_6870130 := by exact prefixLift 6870130
  have htrace : WordTrace (prefixWord ++ tailWord_6870130) baseStart_6870130 baseEnd_6870130 := by
    simpa [prefixWord, tailWord_6870130, baseEnd_6870130] using wordTrace_append hprefix tailTrace_6870130
  have hstable : (prefixWord ++ tailWord_6870130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870130).length < 2 ^ (prefixWord ++ tailWord_6870130).sum := by decide
  have hdescent : baseEnd_6870130 < baseStart_6870130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870151 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_6870151 : Nat := 118140960795 + 6870151 * 2 ^ 59
def prefixEnd_6870151 : Nat := 4983230072969 + 3 ^ 40 * 6870151 * 2
def baseEnd_6870151 : Nat := 3527689631967055236317257

theorem tailTrace_6870151 : CollatzResearch.WordTrace tailWord_6870151 prefixEnd_6870151 3527689631967055236317257 := by
  unfold tailWord_6870151
  simp only [CollatzResearch.WordTrace]
  refine ⟨250574992533623730222466307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167049995022415820148310871 250574992533623730222466307)
  ·
    refine ⟨375862488800435595333699461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250574992533623730222466307 375862488800435595333699461)
    ·
      refine ⟨70474216650081674125068649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 375862488800435595333699461 70474216650081674125068649)
      ·
        refine ⟨52855662487561255593801487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70474216650081674125068649 52855662487561255593801487)
        ·
          refine ⟨79283493731341883390702231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52855662487561255593801487 79283493731341883390702231)
          ·
            refine ⟨118925240597012825086053347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79283493731341883390702231 118925240597012825086053347)
            ·
              refine ⟨178387860895519237629080021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118925240597012825086053347 178387860895519237629080021)
              ·
                refine ⟨4180965489738732131931563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178387860895519237629080021 4180965489738732131931563)
                ·
                  refine ⟨6271448234608098197897345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180965489738732131931563 6271448234608098197897345)
                  ·
                    refine ⟨4703586175956073648423009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271448234608098197897345 4703586175956073648423009)
                    ·
                      refine ⟨3527689631967055236317257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703586175956073648423009 3527689631967055236317257)
                      ·
                        rfl

theorem cell23_6870151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_6870151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870151 prefixEnd_6870151 := by exact prefixLift 6870151
  have htrace : WordTrace (prefixWord ++ tailWord_6870151) baseStart_6870151 baseEnd_6870151 := by
    simpa [prefixWord, tailWord_6870151, baseEnd_6870151] using wordTrace_append hprefix tailTrace_6870151
  have hstable : (prefixWord ++ tailWord_6870151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870151).length < 2 ^ (prefixWord ++ tailWord_6870151).sum := by decide
  have hdescent : baseEnd_6870151 < baseStart_6870151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870168 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 1, 2, 2]
def baseStart_6870168 : Nat := 118140960795 + 6870168 * 2 ^ 59
def prefixEnd_6870168 : Nat := 4983230072969 + 3 ^ 40 * 6870168 * 2
def baseEnd_6870168 : Nat := 3527698361138181669804679

theorem tailTrace_6870168 : CollatzResearch.WordTrace tailWord_6870168 prefixEnd_6870168 3527698361138181669804679 := by
  unfold tailWord_6870168
  simp only [CollatzResearch.WordTrace]
  refine ⟨125287806287281071062917579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167050408383041428083890105 125287806287281071062917579)
  ·
    refine ⟨187931709430921606594376369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125287806287281071062917579 187931709430921606594376369)
    ·
      refine ⟨140948782073191204945782277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187931709430921606594376369 140948782073191204945782277)
      ·
        refine ⟨26427896638723350927334177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140948782073191204945782277 26427896638723350927334177)
        ·
          refine ⟨19820922479042513195500633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26427896638723350927334177 19820922479042513195500633)
          ·
            refine ⟨14865691859281884896625475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19820922479042513195500633 14865691859281884896625475)
            ·
              refine ⟨22298537788922827344938213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14865691859281884896625475 22298537788922827344938213)
              ·
                refine ⟨4180975835423030127175915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22298537788922827344938213 4180975835423030127175915)
                ·
                  refine ⟨6271463753134545190763873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180975835423030127175915 6271463753134545190763873)
                  ·
                    refine ⟨4703597814850908893072905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271463753134545190763873 4703597814850908893072905)
                    ·
                      refine ⟨3527698361138181669804679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703597814850908893072905 3527698361138181669804679)
                      ·
                        rfl

theorem cell23_6870168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_6870168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870168 prefixEnd_6870168 := by exact prefixLift 6870168
  have htrace : WordTrace (prefixWord ++ tailWord_6870168) baseStart_6870168 baseEnd_6870168 := by
    simpa [prefixWord, tailWord_6870168, baseEnd_6870168] using wordTrace_append hprefix tailTrace_6870168
  have hstable : (prefixWord ++ tailWord_6870168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870168).length < 2 ^ (prefixWord ++ tailWord_6870168).sum := by decide
  have hdescent : baseEnd_6870168 < baseStart_6870168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870174 : List Nat := [4, 3, 1, 1, 2, 3, 1, 8]
def baseStart_6870174 : Nat := 118140960795 + 6870174 * 2 ^ 59
def prefixEnd_6870174 : Nat := 4983230072969 + 3 ^ 40 * 6870174 * 2
def baseEnd_6870174 : Nat := 130655608963781801715913

theorem tailTrace_6870174 : CollatzResearch.WordTrace tailWord_6870174 prefixEnd_6870174 130655608963781801715913 := by
  unfold tailWord_6870174
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321978926567550643819197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167050554275026936767035717 31321978926567550643819197)
  ·
    refine ⟨11745742097462831491432199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31321978926567550643819197 11745742097462831491432199)
    ·
      refine ⟨17618613146194247237148299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745742097462831491432199 17618613146194247237148299)
      ·
        refine ⟨26427919719291370855722449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17618613146194247237148299 26427919719291370855722449)
        ·
          refine ⟨19820939789468528141791837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26427919719291370855722449 19820939789468528141791837)
          ·
            refine ⟨7432852421050698053171939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19820939789468528141791837 7432852421050698053171939)
            ·
              refine ⟨11149278631576047079757909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432852421050698053171939 11149278631576047079757909)
              ·
                refine ⟨130655608963781801715913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11149278631576047079757909 130655608963781801715913)
                ·
                  rfl

theorem cell23_6870174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_6870174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870174 prefixEnd_6870174 := by exact prefixLift 6870174
  have htrace : WordTrace (prefixWord ++ tailWord_6870174) baseStart_6870174 baseEnd_6870174 := by
    simpa [prefixWord, tailWord_6870174, baseEnd_6870174] using wordTrace_append hprefix tailTrace_6870174
  have hstable : (prefixWord ++ tailWord_6870174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870174).length < 2 ^ (prefixWord ++ tailWord_6870174).sum := by decide
  have hdescent : baseEnd_6870174 < baseStart_6870174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870194 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_6870194 : Nat := 118140960795 + 6870194 * 2 ^ 59
def prefixEnd_6870194 : Nat := 4983230072969 + 3 ^ 40 * 6870194 * 2
def baseEnd_6870194 : Nat := 3527711711635198568079559

theorem tailTrace_6870194 : CollatzResearch.WordTrace tailWord_6870194 prefixEnd_6870194 3527711711635198568079559 := by
  unfold tailWord_6870194
  simp only [CollatzResearch.WordTrace]
  refine ⟨62644140218116987141570409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167051040581645299044187757 62644140218116987141570409)
  ·
    refine ⟨46983105163587740356177807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62644140218116987141570409 46983105163587740356177807)
    ·
      refine ⟨70474657745381610534266711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46983105163587740356177807 70474657745381610534266711)
      ·
        refine ⟨105711986618072415801400067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70474657745381610534266711 105711986618072415801400067)
        ·
          refine ⟨158567979927108623702100101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105711986618072415801400067 158567979927108623702100101)
          ·
            refine ⟨29731496236332866944143769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158567979927108623702100101 29731496236332866944143769)
            ·
              refine ⟨22298622177249650208107827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29731496236332866944143769 22298622177249650208107827)
              ·
                refine ⟨33447933265874475312161741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22298622177249650208107827 33447933265874475312161741)
                ·
                  refine ⟨12542974974702928242060653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33447933265874475312161741 12542974974702928242060653)
                  ·
                    refine ⟨4703615615513598090772745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12542974974702928242060653 4703615615513598090772745)
                    ·
                      refine ⟨3527711711635198568079559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703615615513598090772745 3527711711635198568079559)
                      ·
                        rfl

theorem cell23_6870194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_6870194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870194 prefixEnd_6870194 := by exact prefixLift 6870194
  have htrace : WordTrace (prefixWord ++ tailWord_6870194) baseStart_6870194 baseEnd_6870194 := by
    simpa [prefixWord, tailWord_6870194, baseEnd_6870194] using wordTrace_append hprefix tailTrace_6870194
  have hstable : (prefixWord ++ tailWord_6870194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870194).length < 2 ^ (prefixWord ++ tailWord_6870194).sum := by decide
  have hdescent : baseEnd_6870194 < baseStart_6870194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870241 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_6870241 : Nat := 118140960795 + 6870241 * 2 ^ 59
def prefixEnd_6870241 : Nat := 4983230072969 + 3 ^ 40 * 6870241 * 2
def baseEnd_6870241 : Nat := 3527735845225959884191843

theorem tailTrace_6870241 : CollatzResearch.WordTrace tailWord_6870241 prefixEnd_6870241 3527735845225959884191843 := by
  unfold tailWord_6870241
  simp only [CollatzResearch.WordTrace]
  refine ⟨250578275103297675593242577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167052183402198450395495051 250578275103297675593242577)
  ·
    refine ⟨187933706327473256694931933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250578275103297675593242577 187933706327473256694931933)
    ·
      refine ⟨70475139872802471260599475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187933706327473256694931933 70475139872802471260599475)
      ·
        refine ⟨105712709809203706890899213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70475139872802471260599475 105712709809203706890899213)
        ·
          refine ⟨39642266178451390084087205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105712709809203706890899213 39642266178451390084087205)
          ·
            refine ⟨7432924908459635640766351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39642266178451390084087205 7432924908459635640766351)
            ·
              refine ⟨11149387362689453461149527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432924908459635640766351 11149387362689453461149527)
              ·
                refine ⟨16724081044034180191724291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11149387362689453461149527 16724081044034180191724291)
                ·
                  refine ⟨25086121566051270287586437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16724081044034180191724291 25086121566051270287586437)
                  ·
                    refine ⟨4703647793634613178922457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25086121566051270287586437 4703647793634613178922457)
                    ·
                      refine ⟨3527735845225959884191843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703647793634613178922457 3527735845225959884191843)
                      ·
                        rfl

theorem cell23_6870241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_6870241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870241 prefixEnd_6870241 := by exact prefixLift 6870241
  have htrace : WordTrace (prefixWord ++ tailWord_6870241) baseStart_6870241 baseEnd_6870241 := by
    simpa [prefixWord, tailWord_6870241, baseEnd_6870241] using wordTrace_append hprefix tailTrace_6870241
  have hstable : (prefixWord ++ tailWord_6870241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870241).length < 2 ^ (prefixWord ++ tailWord_6870241).sum := by decide
  have hdescent : baseEnd_6870241 < baseStart_6870241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870277 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_6870277 : Nat := 118140960795 + 6870277 * 2 ^ 59
def prefixEnd_6870277 : Nat := 4983230072969 + 3 ^ 40 * 6870277 * 2
def baseEnd_6870277 : Nat := 1175918110176507247780559

theorem tailTrace_6870277 : CollatzResearch.WordTrace tailWord_6870277 prefixEnd_6870277 1175918110176507247780559 := by
  unfold tailWord_6870277
  simp only [CollatzResearch.WordTrace]
  refine ⟨250579588131167253741553085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167053058754111502494368723 250579588131167253741553085)
  ·
    refine ⟨93967345549187720153082407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250579588131167253741553085 93967345549187720153082407)
    ·
      refine ⟨140951018323781580229623611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93967345549187720153082407 140951018323781580229623611)
      ·
        refine ⟨211426527485672370344435417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140951018323781580229623611 211426527485672370344435417)
        ·
          refine ⟨158569895614254277758326563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211426527485672370344435417 158569895614254277758326563)
          ·
            refine ⟨237854843421381416637489845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158569895614254277758326563 237854843421381416637489845)
            ·
              refine ⟨22298891570754507809764673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237854843421381416637489845 22298891570754507809764673)
              ·
                refine ⟨16724168678065880857323505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22298891570754507809764673 16724168678065880857323505)
                ·
                  refine ⟨12543126508549410642992629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16724168678065880857323505 12543126508549410642992629)
                  ·
                    refine ⟨1175918110176507247780559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12543126508549410642992629 1175918110176507247780559)
                    ·
                      rfl

theorem cell23_6870277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_6870277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870277 prefixEnd_6870277 := by exact prefixLift 6870277
  have htrace : WordTrace (prefixWord ++ tailWord_6870277) baseStart_6870277 baseEnd_6870277 := by
    simpa [prefixWord, tailWord_6870277, baseEnd_6870277] using wordTrace_append hprefix tailTrace_6870277
  have hstable : (prefixWord ++ tailWord_6870277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870277).length < 2 ^ (prefixWord ++ tailWord_6870277).sum := by decide
  have hdescent : baseEnd_6870277 < baseStart_6870277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870384 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_6870384 : Nat := 118140960795 + 6870384 * 2 ^ 59
def prefixEnd_6870384 : Nat := 4983230072969 + 3 ^ 40 * 6870384 * 2
def baseEnd_6870384 : Nat := 1175936424319850941567895

theorem tailTrace_6870384 : CollatzResearch.WordTrace tailWord_6870384 prefixEnd_6870384 1175936424319850941567895 := by
  unfold tailWord_6870384
  simp only [CollatzResearch.WordTrace]
  refine ⟨125291745370889805507849103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167055660494519740677132137 125291745370889805507849103)
  ·
    refine ⟨187937618056334708261773655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125291745370889805507849103 187937618056334708261773655)
    ·
      refine ⟨281906427084502062392660483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187937618056334708261773655 281906427084502062392660483)
      ·
        refine ⟨422859640626753093588990725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281906427084502062392660483 422859640626753093588990725)
        ·
          refine ⟨79286182617516205047935761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422859640626753093588990725 79286182617516205047935761)
          ·
            refine ⟨59464636963137153785951821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79286182617516205047935761 59464636963137153785951821)
            ·
              refine ⟨22299238861176432669731933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59464636963137153785951821 22299238861176432669731933)
              ·
                refine ⟨8362214572941162251149475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22299238861176432669731933 8362214572941162251149475)
                ·
                  refine ⟨12543321859411743376724213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8362214572941162251149475 12543321859411743376724213)
                  ·
                    refine ⟨1175936424319850941567895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12543321859411743376724213 1175936424319850941567895)
                    ·
                      rfl

theorem cell23_6870384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_6870384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870384 prefixEnd_6870384 := by exact prefixLift 6870384
  have htrace : WordTrace (prefixWord ++ tailWord_6870384) baseStart_6870384 baseEnd_6870384 := by
    simpa [prefixWord, tailWord_6870384, baseEnd_6870384] using wordTrace_append hprefix tailTrace_6870384
  have hstable : (prefixWord ++ tailWord_6870384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870384).length < 2 ^ (prefixWord ++ tailWord_6870384).sum := by decide
  have hdescent : baseEnd_6870384 < baseStart_6870384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870417 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_6870417 : Nat := 118140960795 + 6870417 * 2 ^ 59
def prefixEnd_6870417 : Nat := 4983230072969 + 3 ^ 40 * 6870417 * 2
def baseEnd_6870417 : Nat := 3527826217821151195591033

theorem tailTrace_6870417 : CollatzResearch.WordTrace tailWord_6870417 prefixEnd_6870417 3527826217821151195591033 := by
  unfold tailWord_6870417
  simp only [CollatzResearch.WordTrace]
  refine ⟨250584694350660057651649505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167056462900440038434433003 250584694350660057651649505)
  ·
    refine ⟨187938520762995043238737129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250584694350660057651649505 187938520762995043238737129)
    ·
      refine ⟨140953890572246282429052847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187938520762995043238737129 140953890572246282429052847)
      ·
        refine ⟨211430835858369423643579271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140953890572246282429052847 211430835858369423643579271)
        ·
          refine ⟨317146253787554135465368907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211430835858369423643579271 317146253787554135465368907)
          ·
            refine ⟨475719380681331203198053361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317146253787554135465368907 475719380681331203198053361)
            ·
              refine ⟨356789535510998402398540021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475719380681331203198053361 356789535510998402398540021)
              ·
                refine ⟨33449018954156100224863127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356789535510998402398540021 33449018954156100224863127)
                ·
                  refine ⟨50173528431234150337294691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33449018954156100224863127 50173528431234150337294691)
                  ·
                    refine ⟨75260292646851225505942037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50173528431234150337294691 75260292646851225505942037)
                    ·
                      refine ⟨3527826217821151195591033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75260292646851225505942037 3527826217821151195591033)
                      ·
                        rfl

theorem cell23_6870417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_6870417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870417 prefixEnd_6870417 := by exact prefixLift 6870417
  have htrace : WordTrace (prefixWord ++ tailWord_6870417) baseStart_6870417 baseEnd_6870417 := by
    simpa [prefixWord, tailWord_6870417, baseEnd_6870417] using wordTrace_append hprefix tailTrace_6870417
  have hstable : (prefixWord ++ tailWord_6870417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870417).length < 2 ^ (prefixWord ++ tailWord_6870417).sum := by decide
  have hdescent : baseEnd_6870417 < baseStart_6870417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870504 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6870504 : Nat := 118140960795 + 6870504 * 2 ^ 59
def prefixEnd_6870504 : Nat := 4983230072969 + 3 ^ 40 * 6870504 * 2
def baseEnd_6870504 : Nat := 1175956963546030785067711

theorem tailTrace_6870504 : CollatzResearch.WordTrace tailWord_6870504 prefixEnd_6870504 1175956963546030785067711 := by
  unfold tailWord_6870504
  simp only [CollatzResearch.WordTrace]
  refine ⟨125293933750672435755033283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167058578334229914340044377 125293933750672435755033283)
  ·
    refine ⟨187940900626008653632549925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125293933750672435755033283 187940900626008653632549925)
    ·
      refine ⟨35238918867376622556103111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187940900626008653632549925 35238918867376622556103111)
      ·
        refine ⟨52858378301064933834154667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35238918867376622556103111 52858378301064933834154667)
        ·
          refine ⟨79287567451597400751232001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52858378301064933834154667 79287567451597400751232001)
          ·
            refine ⟨59465675588698050563424001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79287567451597400751232001 59465675588698050563424001)
            ·
              refine ⟨44599256691523537922568001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59465675588698050563424001 44599256691523537922568001)
              ·
                refine ⟨33449442518642653441926001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44599256691523537922568001 33449442518642653441926001)
                ·
                  refine ⟨25087081888981990081444501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33449442518642653441926001 25087081888981990081444501)
                  ·
                    refine ⟨1175956963546030785067711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25087081888981990081444501 1175956963546030785067711)
                    ·
                      rfl

theorem cell23_6870504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6870504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870504 prefixEnd_6870504 := by exact prefixLift 6870504
  have htrace : WordTrace (prefixWord ++ tailWord_6870504) baseStart_6870504 baseEnd_6870504 := by
    simpa [prefixWord, tailWord_6870504, baseEnd_6870504] using wordTrace_append hprefix tailTrace_6870504
  have hstable : (prefixWord ++ tailWord_6870504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870504).length < 2 ^ (prefixWord ++ tailWord_6870504).sum := by decide
  have hdescent : baseEnd_6870504 < baseStart_6870504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870506 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_6870506 : Nat := 118140960795 + 6870506 * 2 ^ 59
def prefixEnd_6870506 : Nat := 4983230072969 + 3 ^ 40 * 6870506 * 2
def baseEnd_6870506 : Nat := 3527871917599401347378125

theorem tailTrace_6870506 : CollatzResearch.WordTrace tailWord_6870506 prefixEnd_6870506 3527871917599401347378125 := by
  unfold tailWord_6870506
  simp only [CollatzResearch.WordTrace]
  refine ⟨62646985111834406462909843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167058626964891750567759581 62646985111834406462909843)
  ·
    refine ⟨93970477667751609694364765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62646985111834406462909843 93970477667751609694364765)
    ·
      refine ⟨35238929125406853635386787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93970477667751609694364765 35238929125406853635386787)
      ·
        refine ⟨52858393688110280453080181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35238929125406853635386787 52858393688110280453080181)
        ·
          refine ⟨4955474408260338792476267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52858393688110280453080181 4955474408260338792476267)
          ·
            refine ⟨7433211612390508188714401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955474408260338792476267 7433211612390508188714401)
            ·
              refine ⟨5574908709292881141535801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433211612390508188714401 5574908709292881141535801)
              ·
                refine ⟨4181181531969660856151851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574908709292881141535801 4181181531969660856151851)
                ·
                  refine ⟨6271772297954491284227777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181181531969660856151851 6271772297954491284227777)
                  ·
                    refine ⟨4703829223465868463170833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6271772297954491284227777 4703829223465868463170833)
                    ·
                      refine ⟨3527871917599401347378125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703829223465868463170833 3527871917599401347378125)
                      ·
                        rfl

theorem cell23_6870506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_6870506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870506 prefixEnd_6870506 := by exact prefixLift 6870506
  have htrace : WordTrace (prefixWord ++ tailWord_6870506) baseStart_6870506 baseEnd_6870506 := by
    simpa [prefixWord, tailWord_6870506, baseEnd_6870506] using wordTrace_append hprefix tailTrace_6870506
  have hstable : (prefixWord ++ tailWord_6870506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870506).length < 2 ^ (prefixWord ++ tailWord_6870506).sum := by decide
  have hdescent : baseEnd_6870506 < baseStart_6870506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870524 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_6870524 : Nat := 118140960795 + 6870524 * 2 ^ 59
def prefixEnd_6870524 : Nat := 4983230072969 + 3 ^ 40 * 6870524 * 2
def baseEnd_6870524 : Nat := 3527881160251182276953041

theorem tailTrace_6870524 : CollatzResearch.WordTrace tailWord_6870524 prefixEnd_6870524 3527881160251182276953041 := by
  unfold tailWord_6870524
  simp only [CollatzResearch.WordTrace]
  refine ⟨125294298480636207462897313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167059064640848276617196417 125294298480636207462897313)
  ·
    refine ⟨93970723860477155597172985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125294298480636207462897313 93970723860477155597172985)
    ·
      refine ⟨70478042895357866697879739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93970723860477155597172985 70478042895357866697879739)
      ·
        refine ⟨105717064343036800046819609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70478042895357866697879739 105717064343036800046819609)
        ·
          refine ⟨79287798257277600035114707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105717064343036800046819609 79287798257277600035114707)
          ·
            refine ⟨118931697385916400052672061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79287798257277600035114707 118931697385916400052672061)
            ·
              refine ⟨44599386519718650019752023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118931697385916400052672061 44599386519718650019752023)
              ·
                refine ⟨66899079779577975029628035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44599386519718650019752023 66899079779577975029628035)
                ·
                  refine ⟨100348619669366962544442053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66899079779577975029628035 100348619669366962544442053)
                  ·
                    refine ⟨18815366188006305477082885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100348619669366962544442053 18815366188006305477082885)
                    ·
                      refine ⟨3527881160251182276953041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18815366188006305477082885 3527881160251182276953041)
                      ·
                        rfl

theorem cell23_6870524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_6870524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870524 prefixEnd_6870524 := by exact prefixLift 6870524
  have htrace : WordTrace (prefixWord ++ tailWord_6870524) baseStart_6870524 baseEnd_6870524 := by
    simpa [prefixWord, tailWord_6870524, baseEnd_6870524] using wordTrace_append hprefix tailTrace_6870524
  have hstable : (prefixWord ++ tailWord_6870524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870524).length < 2 ^ (prefixWord ++ tailWord_6870524).sum := by decide
  have hdescent : baseEnd_6870524 < baseStart_6870524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870561 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6870561 : Nat := 118140960795 + 6870561 * 2 ^ 59
def prefixEnd_6870561 : Nat := 4983230072969 + 3 ^ 40 * 6870561 * 2
def baseEnd_6870561 : Nat := 3527900159035398632190371

theorem tailTrace_6870561 : CollatzResearch.WordTrace tailWord_6870561 prefixEnd_6870561 3527900159035398632190371 := by
  unfold tailWord_6870561
  simp only [CollatzResearch.WordTrace]
  refine ⟨250589946462138370244891537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167059964308092246829927691 250589946462138370244891537)
  ·
    refine ⟨187942459846603777683668653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250589946462138370244891537 187942459846603777683668653)
    ·
      refine ⟨70478422442476416631375745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187942459846603777683668653 70478422442476416631375745)
      ·
        refine ⟨52858816831857312473531809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70478422442476416631375745 52858816831857312473531809)
        ·
          refine ⟨39644112623892984355148857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52858816831857312473531809 39644112623892984355148857)
          ·
            refine ⟨29733084467919738266361643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39644112623892984355148857 29733084467919738266361643)
            ·
              refine ⟨44599626701879607399542465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29733084467919738266361643 44599626701879607399542465)
              ·
                refine ⟨33449720026409705549656849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44599626701879607399542465 33449720026409705549656849)
                ·
                  refine ⟨25087290019807279162242637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33449720026409705549656849 25087290019807279162242637)
                  ·
                    refine ⟨9407733757427729685840989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25087290019807279162242637 9407733757427729685840989)
                    ·
                      refine ⟨3527900159035398632190371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9407733757427729685840989 3527900159035398632190371)
                      ·
                        rfl

theorem cell23_6870561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6870561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870561 prefixEnd_6870561 := by exact prefixLift 6870561
  have htrace : WordTrace (prefixWord ++ tailWord_6870561) baseStart_6870561 baseEnd_6870561 := by
    simpa [prefixWord, tailWord_6870561, baseEnd_6870561] using wordTrace_append hprefix tailTrace_6870561
  have hstable : (prefixWord ++ tailWord_6870561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870561).length < 2 ^ (prefixWord ++ tailWord_6870561).sum := by decide
  have hdescent : baseEnd_6870561 < baseStart_6870561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870568 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 7]
def baseStart_6870568 : Nat := 118140960795 + 6870568 * 2 ^ 59
def prefixEnd_6870568 : Nat := 4983230072969 + 3 ^ 40 * 6870568 * 2
def baseEnd_6870568 : Nat := 391989305933331122755871

theorem tailTrace_6870568 : CollatzResearch.WordTrace tailWord_6870568 prefixEnd_6870568 391989305933331122755871 := by
  unfold tailWord_6870568
  simp only [CollatzResearch.WordTrace]
  refine ⟨125295100886556505220198179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167060134515408673626930905 125295100886556505220198179)
  ·
    refine ⟨187942651329834757830297269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125295100886556505220198179 187942651329834757830297269)
    ·
      refine ⟨17619623562172008546590369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187942651329834757830297269 17619623562172008546590369)
      ·
        refine ⟨13214717671629006409942777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17619623562172008546590369 13214717671629006409942777)
        ·
          refine ⟨9911038253721754807457083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13214717671629006409942777 9911038253721754807457083)
          ·
            refine ⟨14866557380582632211185625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911038253721754807457083 14866557380582632211185625)
            ·
              refine ⟨11149918035436974158389219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14866557380582632211185625 11149918035436974158389219)
              ·
                refine ⟨16724877053155461237583829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11149918035436974158389219 16724877053155461237583829)
                ·
                  refine ⟨391989305933331122755871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16724877053155461237583829 391989305933331122755871)
                  ·
                    rfl

theorem cell23_6870568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_6870568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870568 prefixEnd_6870568 := by exact prefixLift 6870568
  have htrace : WordTrace (prefixWord ++ tailWord_6870568) baseStart_6870568 baseEnd_6870568 := by
    simpa [prefixWord, tailWord_6870568, baseEnd_6870568] using wordTrace_append hprefix tailTrace_6870568
  have hstable : (prefixWord ++ tailWord_6870568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870568).length < 2 ^ (prefixWord ++ tailWord_6870568).sum := by decide
  have hdescent : baseEnd_6870568 < baseStart_6870568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870601 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 6, 2]
def baseStart_6870601 : Nat := 118140960795 + 6870601 * 2 ^ 59
def prefixEnd_6870601 : Nat := 4983230072969 + 3 ^ 40 * 6870601 * 2
def baseEnd_6870601 : Nat := 3527920698261578475690187

theorem tailTrace_6870601 : CollatzResearch.WordTrace tailWord_6870601 prefixEnd_6870601 3527920698261578475690187 := by
  unfold tailWord_6870601
  simp only [CollatzResearch.WordTrace]
  refine ⟨250591405381993457076347657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167060936921328971384231771 250591405381993457076347657)
  ·
    refine ⟨187943554036495092807260743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250591405381993457076347657 187943554036495092807260743)
    ·
      refine ⟨281915331054742639210891115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187943554036495092807260743 281915331054742639210891115)
      ·
        refine ⟨422872996582113958816336673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281915331054742639210891115 422872996582113958816336673)
        ·
          refine ⟨317154747436585469112252505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422872996582113958816336673 317154747436585469112252505)
          ·
            refine ⟨237866060577439101834189379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317154747436585469112252505 237866060577439101834189379)
            ·
              refine ⟨356799090866158652751284069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237866060577439101834189379 356799090866158652751284069)
              ·
                refine ⟨66899829537404747390865763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356799090866158652751284069 66899829537404747390865763)
                ·
                  refine ⟨100349744306107121086298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66899829537404747390865763 100349744306107121086298645)
                  ·
                    refine ⟨4703894264348771300920249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100349744306107121086298645 4703894264348771300920249)
                    ·
                      refine ⟨3527920698261578475690187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4703894264348771300920249 3527920698261578475690187)
                      ·
                        rfl

theorem cell23_6870601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6, 2].length) (baseStart_6870601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870601 prefixEnd_6870601 := by exact prefixLift 6870601
  have htrace : WordTrace (prefixWord ++ tailWord_6870601) baseStart_6870601 baseEnd_6870601 := by
    simpa [prefixWord, tailWord_6870601, baseEnd_6870601] using wordTrace_append hprefix tailTrace_6870601
  have hstable : (prefixWord ++ tailWord_6870601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870601).length < 2 ^ (prefixWord ++ tailWord_6870601).sum := by decide
  have hdescent : baseEnd_6870601 < baseStart_6870601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870628 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_6870628 : Nat := 118140960795 + 6870628 * 2 ^ 59
def prefixEnd_6870628 : Nat := 4983230072969 + 3 ^ 40 * 6870628 * 2
def baseEnd_6870628 : Nat := 1175978187413083290017521

theorem tailTrace_6870628 : CollatzResearch.WordTrace tailWord_6870628 prefixEnd_6870628 1175978187413083290017521 := by
  unfold tailWord_6870628
  simp only [CollatzResearch.WordTrace]
  refine ⟨125296195076447820343790269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167061593435263760458387025 125296195076447820343790269)
  ·
    refine ⟨46986073153667932628921351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125296195076447820343790269 46986073153667932628921351)
    ·
      refine ⟨70479109730501898943382027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46986073153667932628921351 70479109730501898943382027)
      ·
        refine ⟨105718664595752848415073041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70479109730501898943382027 105718664595752848415073041)
        ·
          refine ⟨79288998446814636311304781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105718664595752848415073041 79288998446814636311304781)
          ·
            refine ⟨29733374417555488616739293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79288998446814636311304781 29733374417555488616739293)
            ·
              refine ⟨11150015406583308231277235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29733374417555488616739293 11150015406583308231277235)
              ·
                refine ⟨16725023109874962346915853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11150015406583308231277235 16725023109874962346915853)
                ·
                  refine ⟨6271883666203110880093445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16725023109874962346915853 6271883666203110880093445)
                  ·
                    refine ⟨1175978187413083290017521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271883666203110880093445 1175978187413083290017521)
                    ·
                      rfl

theorem cell23_6870628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_6870628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870628 prefixEnd_6870628 := by exact prefixLift 6870628
  have htrace : WordTrace (prefixWord ++ tailWord_6870628) baseStart_6870628 baseEnd_6870628 := by
    simpa [prefixWord, tailWord_6870628, baseEnd_6870628] using wordTrace_append hprefix tailTrace_6870628
  have hstable : (prefixWord ++ tailWord_6870628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870628).length < 2 ^ (prefixWord ++ tailWord_6870628).sum := by decide
  have hdescent : baseEnd_6870628 < baseStart_6870628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870691 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4]
def baseStart_6870691 : Nat := 118140960795 + 6870691 * 2 ^ 59
def prefixEnd_6870691 : Nat := 4983230072969 + 3 ^ 40 * 6870691 * 2
def baseEnd_6870691 : Nat := 3527966911520483123564773

theorem tailTrace_6870691 : CollatzResearch.WordTrace tailWord_6870691 prefixEnd_6870691 3527966911520483123564773 := by
  unfold tailWord_6870691
  simp only [CollatzResearch.WordTrace]
  refine ⟨250594687951667402447123927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167063125301111601631415951 250594687951667402447123927)
  ·
    refine ⟨375892031927501103670685891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250594687951667402447123927 375892031927501103670685891)
    ·
      refine ⟨563838047891251655506028837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375892031927501103670685891 563838047891251655506028837)
      ·
        refine ⟨105719633979609685407380407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 563838047891251655506028837 105719633979609685407380407)
        ·
          refine ⟨158579450969414528111070611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105719633979609685407380407 158579450969414528111070611)
          ·
            refine ⟨237869176454121792166605917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158579450969414528111070611 237869176454121792166605917)
            ·
              refine ⟨89200941170295672062477219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237869176454121792166605917 89200941170295672062477219)
              ·
                refine ⟨133801411755443508093715829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89200941170295672062477219 133801411755443508093715829)
                ·
                  refine ⟨12543882352072828883785859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133801411755443508093715829 12543882352072828883785859)
                  ·
                    refine ⟨18815823528109243325678789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12543882352072828883785859 18815823528109243325678789)
                    ·
                      refine ⟨3527966911520483123564773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18815823528109243325678789 3527966911520483123564773)
                      ·
                        rfl

theorem cell23_6870691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_6870691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870691 prefixEnd_6870691 := by exact prefixLift 6870691
  have htrace : WordTrace (prefixWord ++ tailWord_6870691) baseStart_6870691 baseEnd_6870691 := by
    simpa [prefixWord, tailWord_6870691, baseEnd_6870691] using wordTrace_append hprefix tailTrace_6870691
  have hstable : (prefixWord ++ tailWord_6870691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870691).length < 2 ^ (prefixWord ++ tailWord_6870691).sum := by decide
  have hdescent : baseEnd_6870691 < baseStart_6870691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870718 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6870718 : Nat := 118140960795 + 6870718 * 2 ^ 59
def prefixEnd_6870718 : Nat := 4983230072969 + 3 ^ 40 * 6870718 * 2
def baseEnd_6870718 : Nat := 1175993591832718172642383

theorem tailTrace_6870718 : CollatzResearch.WordTrace tailWord_6870718 prefixEnd_6870718 1175993591832718172642383 := by
  unfold tailWord_6870718
  simp only [CollatzResearch.WordTrace]
  refine ⟨31324459090321198257294601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167063781815046390705571205 31324459090321198257294601)
  ·
    refine ⟨23493344317740898692970951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31324459090321198257294601 23493344317740898692970951)
    ·
      refine ⟨35240016476611348039456427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23493344317740898692970951 35240016476611348039456427)
      ·
        refine ⟨52860024714917022059184641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35240016476611348039456427 52860024714917022059184641)
        ·
          refine ⟨39645018536187766544388481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52860024714917022059184641 39645018536187766544388481)
          ·
            refine ⟨29733763902140824908291361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39645018536187766544388481 29733763902140824908291361)
            ·
              refine ⟨22300322926605618681218521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29733763902140824908291361 22300322926605618681218521)
              ·
                refine ⟨16725242194954214010913891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22300322926605618681218521 16725242194954214010913891)
                ·
                  refine ⟨25087863292431321016370837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16725242194954214010913891 25087863292431321016370837)
                  ·
                    refine ⟨1175993591832718172642383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25087863292431321016370837 1175993591832718172642383)
                    ·
                      rfl

theorem cell23_6870718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6870718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870718 prefixEnd_6870718 := by exact prefixLift 6870718
  have htrace : WordTrace (prefixWord ++ tailWord_6870718) baseStart_6870718 baseEnd_6870718 := by
    simpa [prefixWord, tailWord_6870718, baseEnd_6870718] using wordTrace_append hprefix tailTrace_6870718
  have hstable : (prefixWord ++ tailWord_6870718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870718).length < 2 ^ (prefixWord ++ tailWord_6870718).sum := by decide
  have hdescent : baseEnd_6870718 < baseStart_6870718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870765 : List Nat := [1, 5, 1, 2, 1, 4, 2, 7]
def baseStart_6870765 : Nat := 118140960795 + 6870765 * 2 ^ 59
def prefixEnd_6870765 : Nat := 4983230072969 + 3 ^ 40 * 6870765 * 2
def baseEnd_6870765 : Nat := 130666848484774660519979

theorem tailTrace_6870765 : CollatzResearch.WordTrace tailWord_6870765 prefixEnd_6870765 130666848484774660519979 := by
  unfold tailWord_6870765
  simp only [CollatzResearch.WordTrace]
  refine ⟨250597386953399313085317749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167064924635599542056878499 250597386953399313085317749)
  ·
    refine ⟨23493505026881185601748539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250597386953399313085317749 23493505026881185601748539)
    ·
      refine ⟨35240257540321778402622809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23493505026881185601748539 35240257540321778402622809)
      ·
        refine ⟨26430193155241333801967107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35240257540321778402622809 26430193155241333801967107)
        ·
          refine ⟨39645289732862000702950661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26430193155241333801967107 39645289732862000702950661)
          ·
            refine ⟨7433491824911625131803249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39645289732862000702950661 7433491824911625131803249)
            ·
              refine ⟨5575118868683718848852437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433491824911625131803249 5575118868683718848852437)
              ·
                refine ⟨130666848484774660519979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5575118868683718848852437 130666848484774660519979)
                ·
                  rfl

theorem cell23_6870765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 7].length) (baseStart_6870765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870765 prefixEnd_6870765 := by exact prefixLift 6870765
  have htrace : WordTrace (prefixWord ++ tailWord_6870765) baseStart_6870765 baseEnd_6870765 := by
    simpa [prefixWord, tailWord_6870765, baseEnd_6870765] using wordTrace_append hprefix tailTrace_6870765
  have hstable : (prefixWord ++ tailWord_6870765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870765).length < 2 ^ (prefixWord ++ tailWord_6870765).sum := by decide
  have hdescent : baseEnd_6870765 < baseStart_6870765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870771 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_6870771 : Nat := 118140960795 + 6870771 * 2 ^ 59
def prefixEnd_6870771 : Nat := 4983230072969 + 3 ^ 40 * 6870771 * 2
def baseEnd_6870771 : Nat := 3528007989972842810564405

theorem tailTrace_6870771 : CollatzResearch.WordTrace tailWord_6870771 prefixEnd_6870771 3528007989972842810564405 := by
  unfold tailWord_6870771
  simp only [CollatzResearch.WordTrace]
  refine ⟨250597605791377576110036167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167065070527585050740024111 250597605791377576110036167)
  ·
    refine ⟨375896408687066364165054251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250597605791377576110036167 375896408687066364165054251)
    ·
      refine ⟨563844613030599546247581377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375896408687066364165054251 563844613030599546247581377)
      ·
        refine ⟨422883459772949659685686033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563844613030599546247581377 422883459772949659685686033)
        ·
          refine ⟨317162594829712244764264525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422883459772949659685686033 317162594829712244764264525)
          ·
            refine ⟨118935973061142091786599197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317162594829712244764264525 118935973061142091786599197)
            ·
              refine ⟨44600989897928284419974699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118935973061142091786599197 44600989897928284419974699)
              ·
                refine ⟨66901484846892426629962049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44600989897928284419974699 66901484846892426629962049)
                ·
                  refine ⟨50176113635169319972471537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66901484846892426629962049 50176113635169319972471537)
                  ·
                    refine ⟨37632085226376989979353653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50176113635169319972471537 37632085226376989979353653)
                    ·
                      refine ⟨3528007989972842810564405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37632085226376989979353653 3528007989972842810564405)
                      ·
                        rfl

theorem cell23_6870771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_6870771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870771 prefixEnd_6870771 := by exact prefixLift 6870771
  have htrace : WordTrace (prefixWord ++ tailWord_6870771) baseStart_6870771 baseEnd_6870771 := by
    simpa [prefixWord, tailWord_6870771, baseEnd_6870771] using wordTrace_append hprefix tailTrace_6870771
  have hstable : (prefixWord ++ tailWord_6870771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870771).length < 2 ^ (prefixWord ++ tailWord_6870771).sum := by decide
  have hdescent : baseEnd_6870771 < baseStart_6870771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870801 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_6870801 : Nat := 118140960795 + 6870801 * 2 ^ 59
def prefixEnd_6870801 : Nat := 4983230072969 + 3 ^ 40 * 6870801 * 2
def baseEnd_6870801 : Nat := 3528023394392477693189267

theorem tailTrace_6870801 : CollatzResearch.WordTrace tailWord_6870801 prefixEnd_6870801 3528023394392477693189267 := by
  unfold tailWord_6870801
  simp only [CollatzResearch.WordTrace]
  refine ⟨250598699981268891233628257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167065799987512594155752171 250598699981268891233628257)
  ·
    refine ⟨187949024985951668425221193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250598699981268891233628257 187949024985951668425221193)
    ·
      refine ⟨140961768739463751318915895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187949024985951668425221193 140961768739463751318915895)
      ·
        refine ⟨211442653109195626978373843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140961768739463751318915895 211442653109195626978373843)
        ·
          refine ⟨317163979663793440467560765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211442653109195626978373843 317163979663793440467560765)
          ·
            refine ⟨118936492373922540175335287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317163979663793440467560765 118936492373922540175335287)
            ·
              refine ⟨178404738560883810263002931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118936492373922540175335287 178404738560883810263002931)
              ·
                refine ⟨267607107841325715394504397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178404738560883810263002931 267607107841325715394504397)
                ·
                  refine ⟨100352665440497143272939149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267607107841325715394504397 100352665440497143272939149)
                  ·
                    refine ⟨37632249540186428727352181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100352665440497143272939149 37632249540186428727352181)
                    ·
                      refine ⟨3528023394392477693189267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37632249540186428727352181 3528023394392477693189267)
                      ·
                        rfl

theorem cell23_6870801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_6870801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870801 prefixEnd_6870801 := by exact prefixLift 6870801
  have htrace : WordTrace (prefixWord ++ tailWord_6870801) baseStart_6870801 baseEnd_6870801 := by
    simpa [prefixWord, tailWord_6870801, baseEnd_6870801] using wordTrace_append hprefix tailTrace_6870801
  have hstable : (prefixWord ++ tailWord_6870801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870801).length < 2 ^ (prefixWord ++ tailWord_6870801).sum := by decide
  have hdescent : baseEnd_6870801 < baseStart_6870801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870815 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 1, 4, 2]
def baseStart_6870815 : Nat := 118140960795 + 6870815 * 2 ^ 59
def prefixEnd_6870815 : Nat := 4983230072969 + 3 ^ 40 * 6870815 * 2
def baseEnd_6870815 : Nat := 3528030583121640638414203

theorem tailTrace_6870815 : CollatzResearch.WordTrace tailWord_6870815 prefixEnd_6870815 3528030583121640638414203 := by
  unfold tailWord_6870815
  simp only [CollatzResearch.WordTrace]
  refine ⟨250599210603218171624637899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167066140402145447749758599 250599210603218171624637899)
  ·
    refine ⟨375898815904827257436956849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250599210603218171624637899 375898815904827257436956849)
    ·
      refine ⟨281924111928620443077717637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375898815904827257436956849 281924111928620443077717637)
      ·
        refine ⟨52860770986616333077072057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281924111928620443077717637 52860770986616333077072057)
        ·
          refine ⟨39645578239962249807804043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52860770986616333077072057 39645578239962249807804043)
          ·
            refine ⟨59468367359943374711706065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39645578239962249807804043 59468367359943374711706065)
            ·
              refine ⟨44601275519957531033779549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59468367359943374711706065 44601275519957531033779549)
              ·
                refine ⟨16725478319984074137667331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44601275519957531033779549 16725478319984074137667331)
                ·
                  refine ⟨25088217479976111206500997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16725478319984074137667331 25088217479976111206500997)
                  ·
                    refine ⟨4704040777495520851218937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25088217479976111206500997 4704040777495520851218937)
                    ·
                      refine ⟨3528030583121640638414203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704040777495520851218937 3528030583121640638414203)
                      ·
                        rfl

theorem cell23_6870815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_6870815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870815 prefixEnd_6870815 := by exact prefixLift 6870815
  have htrace : WordTrace (prefixWord ++ tailWord_6870815) baseStart_6870815 baseEnd_6870815 := by
    simpa [prefixWord, tailWord_6870815, baseEnd_6870815] using wordTrace_append hprefix tailTrace_6870815
  have hstable : (prefixWord ++ tailWord_6870815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870815).length < 2 ^ (prefixWord ++ tailWord_6870815).sum := by decide
  have hdescent : baseEnd_6870815 < baseStart_6870815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870818 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6870818 : Nat := 118140960795 + 6870818 * 2 ^ 59
def prefixEnd_6870818 : Nat := 4983230072969 + 3 ^ 40 * 6870818 * 2
def baseEnd_6870818 : Nat := 3528032123563604126676689

theorem tailTrace_6870818 : CollatzResearch.WordTrace tailWord_6870818 prefixEnd_6870818 3528032123563604126676689 := by
  unfold tailWord_6870818
  simp only [CollatzResearch.WordTrace]
  refine ⟨62649830005551825784249277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167066213348138202091331405 62649830005551825784249277)
  ·
    refine ⟨23493686252081934669093479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62649830005551825784249277 23493686252081934669093479)
    ·
      refine ⟨35240529378122902003640219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23493686252081934669093479 35240529378122902003640219)
      ·
        refine ⟨52860794067184353005460329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35240529378122902003640219 52860794067184353005460329)
        ·
          refine ⟨39645595550388264754095247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52860794067184353005460329 39645595550388264754095247)
          ·
            refine ⟨59468393325582397131142871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39645595550388264754095247 59468393325582397131142871)
            ·
              refine ⟨89202589988373595696714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59468393325582397131142871 89202589988373595696714307)
              ·
                refine ⟨133803884982560393545071461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89202589988373595696714307 133803884982560393545071461)
                ·
                  refine ⟨25088228434230073789700899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133803884982560393545071461 25088228434230073789700899)
                  ·
                    refine ⟨37632342651345110684551349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25088228434230073789700899 37632342651345110684551349)
                    ·
                      refine ⟨3528032123563604126676689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37632342651345110684551349 3528032123563604126676689)
                      ·
                        rfl

theorem cell23_6870818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6870818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870818 prefixEnd_6870818 := by exact prefixLift 6870818
  have htrace : WordTrace (prefixWord ++ tailWord_6870818) baseStart_6870818 baseEnd_6870818 := by
    simpa [prefixWord, tailWord_6870818, baseEnd_6870818] using wordTrace_append hprefix tailTrace_6870818
  have hstable : (prefixWord ++ tailWord_6870818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870818).length < 2 ^ (prefixWord ++ tailWord_6870818).sum := by decide
  have hdescent : baseEnd_6870818 < baseStart_6870818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870836 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_6870836 : Nat := 118140960795 + 6870836 * 2 ^ 59
def prefixEnd_6870836 : Nat := 4983230072969 + 3 ^ 40 * 6870836 * 2
def baseEnd_6870836 : Nat := 3528041366215385056251607

theorem tailTrace_6870836 : CollatzResearch.WordTrace tailWord_6870836 prefixEnd_6870836 3528041366215385056251607 := by
  unfold tailWord_6870836
  simp only [CollatzResearch.WordTrace]
  refine ⟨125299988268071046105576181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167066651024094728140768241 125299988268071046105576181)
  ·
    refine ⟨11746873900131660572397767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125299988268071046105576181 11746873900131660572397767)
    ·
      refine ⟨17620310850197490858596651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11746873900131660572397767 17620310850197490858596651)
      ·
        refine ⟨26430466275296236287894977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17620310850197490858596651 26430466275296236287894977)
        ·
          refine ⟨19822849706472177215921233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26430466275296236287894977 19822849706472177215921233)
          ·
            refine ⟨14867137279854132911940925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19822849706472177215921233 14867137279854132911940925)
            ·
              refine ⟨5575176479945299841977847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14867137279854132911940925 5575176479945299841977847)
              ·
                refine ⟨8362764719917949762966771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575176479945299841977847 8362764719917949762966771)
                ·
                  refine ⟨12544147079876924644450157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8362764719917949762966771 12544147079876924644450157)
                  ·
                    refine ⟨4704055154953846741668809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12544147079876924644450157 4704055154953846741668809)
                    ·
                      refine ⟨3528041366215385056251607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704055154953846741668809 3528041366215385056251607)
                      ·
                        rfl

theorem cell23_6870836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_6870836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870836 prefixEnd_6870836 := by exact prefixLift 6870836
  have htrace : WordTrace (prefixWord ++ tailWord_6870836) baseStart_6870836 baseEnd_6870836 := by
    simpa [prefixWord, tailWord_6870836, baseEnd_6870836] using wordTrace_append hprefix tailTrace_6870836
  have hstable : (prefixWord ++ tailWord_6870836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870836).length < 2 ^ (prefixWord ++ tailWord_6870836).sum := by decide
  have hdescent : baseEnd_6870836 < baseStart_6870836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870865 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_6870865 : Nat := 118140960795 + 6870865 * 2 ^ 59
def prefixEnd_6870865 : Nat := 4983230072969 + 3 ^ 40 * 6870865 * 2
def baseEnd_6870865 : Nat := 3528056257154365442788973

theorem tailTrace_6870865 : CollatzResearch.WordTrace tailWord_6870865 prefixEnd_6870865 3528056257154365442788973 := by
  unfold tailWord_6870865
  simp only [CollatzResearch.WordTrace]
  refine ⟨250601034253037030163958049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167067356168691353442638699 250601034253037030163958049)
  ·
    refine ⟨187950775689777772622968537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250601034253037030163958049 187950775689777772622968537)
    ·
      refine ⟨140963081767333329467226403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187950775689777772622968537 140963081767333329467226403)
      ·
        refine ⟨211444622650999994200839605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140963081767333329467226403 211444622650999994200839605)
        ·
          refine ⟨19822933373531249456328713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211444622650999994200839605 19822933373531249456328713)
          ·
            refine ⟨14867200030148437092246535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19822933373531249456328713 14867200030148437092246535)
            ·
              refine ⟨22300800045222655638369803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867200030148437092246535 22300800045222655638369803)
              ·
                refine ⟨33451200067833983457554705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22300800045222655638369803 33451200067833983457554705)
                ·
                  refine ⟨25088400050875487593166029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33451200067833983457554705 25088400050875487593166029)
                  ·
                    refine ⟨9408150019078307847437261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25088400050875487593166029 9408150019078307847437261)
                    ·
                      refine ⟨3528056257154365442788973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9408150019078307847437261 3528056257154365442788973)
                      ·
                        rfl

theorem cell23_6870865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_6870865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870865 prefixEnd_6870865 := by exact prefixLift 6870865
  have htrace : WordTrace (prefixWord ++ tailWord_6870865) baseStart_6870865 baseEnd_6870865 := by
    simpa [prefixWord, tailWord_6870865, baseEnd_6870865] using wordTrace_append hprefix tailTrace_6870865
  have hstable : (prefixWord ++ tailWord_6870865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870865).length < 2 ^ (prefixWord ++ tailWord_6870865).sum := by decide
  have hdescent : baseEnd_6870865 < baseStart_6870865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870905 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 4, 4, 2]
def baseStart_6870905 : Nat := 118140960795 + 6870905 * 2 ^ 59
def prefixEnd_6870905 : Nat := 4983230072969 + 3 ^ 40 * 6870905 * 2
def baseEnd_6870905 : Nat := 3528076796380545286288789

theorem tailTrace_6870905 : CollatzResearch.WordTrace tailWord_6870905 prefixEnd_6870905 3528076796380545286288789 := by
  unfold tailWord_6870905
  simp only [CollatzResearch.WordTrace]
  refine ⟨250602493172892116995414169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167068328781928077996942779 250602493172892116995414169)
  ·
    refine ⟨187951869879669087746560627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250602493172892116995414169 187951869879669087746560627)
    ·
      refine ⟨281927804819503631619840941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187951869879669087746560627 281927804819503631619840941)
      ·
        refine ⟨105722926807313861857440353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281927804819503631619840941 105722926807313861857440353)
        ·
          refine ⟨79292195105485396393080265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105722926807313861857440353 79292195105485396393080265)
          ·
            refine ⟨59469146329114047294810199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79292195105485396393080265 59469146329114047294810199)
            ·
              refine ⟨89203719493671070942215299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59469146329114047294810199 89203719493671070942215299)
              ·
                refine ⟨133805579240506606413322949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89203719493671070942215299 133805579240506606413322949)
                ·
                  refine ⟨25088546107594988702498053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133805579240506606413322949 25088546107594988702498053)
                  ·
                    refine ⟨4704102395174060381718385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25088546107594988702498053 4704102395174060381718385)
                    ·
                      refine ⟨3528076796380545286288789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704102395174060381718385 3528076796380545286288789)
                      ·
                        rfl

theorem cell23_6870905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_6870905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870905 prefixEnd_6870905 := by exact prefixLift 6870905
  have htrace : WordTrace (prefixWord ++ tailWord_6870905) baseStart_6870905 baseEnd_6870905 := by
    simpa [prefixWord, tailWord_6870905, baseEnd_6870905] using wordTrace_append hprefix tailTrace_6870905
  have hstable : (prefixWord ++ tailWord_6870905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870905).length < 2 ^ (prefixWord ++ tailWord_6870905).sum := by decide
  have hdescent : baseEnd_6870905 < baseStart_6870905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870915 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 3, 4]
def baseStart_6870915 : Nat := 118140960795 + 6870915 * 2 ^ 59
def prefixEnd_6870915 : Nat := 4983230072969 + 3 ^ 40 * 6870915 * 2
def baseEnd_6870915 : Nat := 1176027310395696749054581

theorem tailTrace_6870915 : CollatzResearch.WordTrace tailWord_6870915 prefixEnd_6870915 1176027310395696749054581 := by
  unfold tailWord_6870915
  simp only [CollatzResearch.WordTrace]
  refine ⟨250602857902855888703278199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167068571935237259135518799 250602857902855888703278199)
  ·
    refine ⟨375904286854283833054917299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250602857902855888703278199 375904286854283833054917299)
    ·
      refine ⟨563856430281425749582375949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375904286854283833054917299 563856430281425749582375949)
      ·
        refine ⟨211446161355534656093390981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563856430281425749582375949 211446161355534656093390981)
        ·
          refine ⟨39646155254162748017510809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211446161355534656093390981 39646155254162748017510809)
          ·
            refine ⟨29734616440622061013133107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39646155254162748017510809 29734616440622061013133107)
            ·
              refine ⟨44601924660933091519699661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29734616440622061013133107 44601924660933091519699661)
              ·
                refine ⟨16725721747849909319887373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44601924660933091519699661 16725721747849909319887373)
                ·
                  refine ⟨6272145655443715994957765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16725721747849909319887373 6272145655443715994957765)
                  ·
                    refine ⟨1176027310395696749054581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272145655443715994957765 1176027310395696749054581)
                    ·
                      rfl

theorem cell23_6870915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 4].length) (baseStart_6870915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870915 prefixEnd_6870915 := by exact prefixLift 6870915
  have htrace : WordTrace (prefixWord ++ tailWord_6870915) baseStart_6870915 baseEnd_6870915 := by
    simpa [prefixWord, tailWord_6870915, baseEnd_6870915] using wordTrace_append hprefix tailTrace_6870915
  have hstable : (prefixWord ++ tailWord_6870915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870915).length < 2 ^ (prefixWord ++ tailWord_6870915).sum := by decide
  have hdescent : baseEnd_6870915 < baseStart_6870915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6870932 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_6870932 : Nat := 118140960795 + 6870932 * 2 ^ 59
def prefixEnd_6870932 : Nat := 4983230072969 + 3 ^ 40 * 6870932 * 2
def baseEnd_6870932 : Nat := 1176030220119405560217055

theorem tailTrace_6870932 : CollatzResearch.WordTrace tailWord_6870932 prefixEnd_6870932 1176030220119405560217055 := by
  unfold tailWord_6870932
  simp only [CollatzResearch.WordTrace]
  refine ⟨125301738971897150303323525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167068985295862867071098033 125301738971897150303323525)
  ·
    refine ⟨23494076057230715681873161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125301738971897150303323525 23494076057230715681873161)
    ·
      refine ⟨17620557042923036761404871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23494076057230715681873161 17620557042923036761404871)
      ·
        refine ⟨26430835564384555142107307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17620557042923036761404871 26430835564384555142107307)
        ·
          refine ⟨39646253346576832713160961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26430835564384555142107307 39646253346576832713160961)
          ·
            refine ⟨29734690009932624534870721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39646253346576832713160961 29734690009932624534870721)
            ·
              refine ⟨22301017507449468401153041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29734690009932624534870721 22301017507449468401153041)
              ·
                refine ⟨16725763130587101300864781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22301017507449468401153041 16725763130587101300864781)
                ·
                  refine ⟨6272161173970162987824293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16725763130587101300864781 6272161173970162987824293)
                  ·
                    refine ⟨1176030220119405560217055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272161173970162987824293 1176030220119405560217055)
                    ·
                      rfl

theorem cell23_6870932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_6870932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6870932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6870932 prefixEnd_6870932 := by exact prefixLift 6870932
  have htrace : WordTrace (prefixWord ++ tailWord_6870932) baseStart_6870932 baseEnd_6870932 := by
    simpa [prefixWord, tailWord_6870932, baseEnd_6870932] using wordTrace_append hprefix tailTrace_6870932
  have hstable : (prefixWord ++ tailWord_6870932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6870932).length < 2 ^ (prefixWord ++ tailWord_6870932).sum := by decide
  have hdescent : baseEnd_6870932 < baseStart_6870932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6870932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871060 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6871060 : Nat := 118140960795 + 6871060 * 2 ^ 59
def prefixEnd_6871060 : Nat := 4983230072969 + 3 ^ 40 * 6871060 * 2
def baseEnd_6871060 : Nat := 1176052128627330726616859

theorem tailTrace_6871060 : CollatzResearch.WordTrace tailWord_6871060 prefixEnd_6871060 1176052128627330726616859 := by
  unfold tailWord_6871060
  simp only [CollatzResearch.WordTrace]
  refine ⟨125304073243665289233653317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167072097658220385644871089 125304073243665289233653317)
  ·
    refine ⟨23494513733187241731309997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125304073243665289233653317 23494513733187241731309997)
    ·
      refine ⟨8810442649945215649241249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23494513733187241731309997 8810442649945215649241249)
      ·
        refine ⟨6607831987458911736930937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810442649945215649241249 6607831987458911736930937)
        ·
          refine ⟨4955873990594183802698203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6607831987458911736930937 4955873990594183802698203)
          ·
            refine ⟨7433810985891275704047305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955873990594183802698203 7433810985891275704047305)
            ·
              refine ⟨5575358239418456778035479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433810985891275704047305 5575358239418456778035479)
              ·
                refine ⟨8363037359127685167053219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575358239418456778035479 8363037359127685167053219)
                ·
                  refine ⟨12544556038691527750579829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363037359127685167053219 12544556038691527750579829)
                  ·
                    refine ⟨1176052128627330726616859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12544556038691527750579829 1176052128627330726616859)
                    ·
                      rfl

theorem cell23_6871060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6871060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871060 prefixEnd_6871060 := by exact prefixLift 6871060
  have htrace : WordTrace (prefixWord ++ tailWord_6871060) baseStart_6871060 baseEnd_6871060 := by
    simpa [prefixWord, tailWord_6871060, baseEnd_6871060] using wordTrace_append hprefix tailTrace_6871060
  have hstable : (prefixWord ++ tailWord_6871060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871060).length < 2 ^ (prefixWord ++ tailWord_6871060).sum := by decide
  have hdescent : baseEnd_6871060 < baseStart_6871060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871063 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6871063 : Nat := 118140960795 + 6871063 * 2 ^ 59
def prefixEnd_6871063 : Nat := 4983230072969 + 3 ^ 40 * 6871063 * 2
def baseEnd_6871063 : Nat := 3528157926323955668113063

theorem tailTrace_6871063 : CollatzResearch.WordTrace tailWord_6871063 prefixEnd_6871063 3528157926323955668113063 := by
  unfold tailWord_6871063
  simp only [CollatzResearch.WordTrace]
  refine ⟨250608255906319709979665843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167072170604213139986443895 250608255906319709979665843)
  ·
    refine ⟨375912383859479564969498765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250608255906319709979665843 375912383859479564969498765)
    ·
      refine ⟨140967143947304836863562037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375912383859479564969498765 140967143947304836863562037)
      ·
        refine ⟨13215669745059828455958941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140967143947304836863562037 13215669745059828455958941)
        ·
          refine ⟨4955876154397435670984603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13215669745059828455958941 4955876154397435670984603)
          ·
            refine ⟨7433814231596153506476905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955876154397435670984603 7433814231596153506476905)
            ·
              refine ⟨5575360673697115129857679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433814231596153506476905 5575360673697115129857679)
              ·
                refine ⟨8363041010545672694786519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575360673697115129857679 8363041010545672694786519)
                ·
                  refine ⟨12544561515818509042179779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363041010545672694786519 12544561515818509042179779)
                  ·
                    refine ⟨18816842273727763563269669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12544561515818509042179779 18816842273727763563269669)
                    ·
                      refine ⟨3528157926323955668113063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18816842273727763563269669 3528157926323955668113063)
                      ·
                        rfl

theorem cell23_6871063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6871063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871063 prefixEnd_6871063 := by exact prefixLift 6871063
  have htrace : WordTrace (prefixWord ++ tailWord_6871063) baseStart_6871063 baseEnd_6871063 := by
    simpa [prefixWord, tailWord_6871063, baseEnd_6871063] using wordTrace_append hprefix tailTrace_6871063
  have hstable : (prefixWord ++ tailWord_6871063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871063).length < 2 ^ (prefixWord ++ tailWord_6871063).sum := by decide
  have hdescent : baseEnd_6871063 < baseStart_6871063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871066 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_6871066 : Nat := 118140960795 + 6871066 * 2 ^ 59
def prefixEnd_6871066 : Nat := 4983230072969 + 3 ^ 40 * 6871066 * 2
def baseEnd_6871066 : Nat := 3528159466765919156375549

theorem tailTrace_6871066 : CollatzResearch.WordTrace tailWord_6871066 prefixEnd_6871066 3528159466765919156375549 := by
  unfold tailWord_6871066
  simp only [CollatzResearch.WordTrace]
  refine ⟨62652091331327210373006263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167072243550205894328016701 62652091331327210373006263)
  ·
    refine ⟨93978136996990815559509395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62652091331327210373006263 93978136996990815559509395)
    ·
      refine ⟨140967205495486223339264093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93978136996990815559509395 140967205495486223339264093)
      ·
        refine ⟨52862702060807333752224035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140967205495486223339264093 52862702060807333752224035)
        ·
          refine ⟨79294053091211000628336053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52862702060807333752224035 79294053091211000628336053)
          ·
            refine ⟨7433817477301031308906505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79294053091211000628336053 7433817477301031308906505)
            ·
              refine ⟨5575363107975773481679879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433817477301031308906505 5575363107975773481679879)
              ·
                refine ⟨8363044661963660222519819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575363107975773481679879 8363044661963660222519819)
                ·
                  refine ⟨12544566992945490333779729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363044661963660222519819 12544566992945490333779729)
                  ·
                    refine ⟨9408425244709117750334797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12544566992945490333779729 9408425244709117750334797)
                    ·
                      refine ⟨3528159466765919156375549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9408425244709117750334797 3528159466765919156375549)
                      ·
                        rfl

theorem cell23_6871066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_6871066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871066 prefixEnd_6871066 := by exact prefixLift 6871066
  have htrace : WordTrace (prefixWord ++ tailWord_6871066) baseStart_6871066 baseEnd_6871066 := by
    simpa [prefixWord, tailWord_6871066, baseEnd_6871066] using wordTrace_append hprefix tailTrace_6871066
  have hstable : (prefixWord ++ tailWord_6871066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871066).length < 2 ^ (prefixWord ++ tailWord_6871066).sum := by decide
  have hdescent : baseEnd_6871066 < baseStart_6871066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871095 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 2, 6]
def baseStart_6871095 : Nat := 118140960795 + 6871095 * 2 ^ 59
def prefixEnd_6871095 : Nat := 4983230072969 + 3 ^ 40 * 6871095 * 2
def baseEnd_6871095 : Nat := 1176058119234966514304305

theorem tailTrace_6871095 : CollatzResearch.WordTrace tailWord_6871095 prefixEnd_6871095 1176058119234966514304305 := by
  unfold tailWord_6871095
  simp only [CollatzResearch.WordTrace]
  refine ⟨250609423042203779444830739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167072948694802519629887159 250609423042203779444830739)
  ·
    refine ⟨375914134563305669167246109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250609423042203779444830739 375914134563305669167246109)
    ·
      refine ⟨140967800461239625937717291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375914134563305669167246109 140967800461239625937717291)
      ·
        refine ⟨211451700691859438906575937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140967800461239625937717291 211451700691859438906575937)
        ·
          refine ⟨158588775518894579179931953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211451700691859438906575937 158588775518894579179931953)
          ·
            refine ⟨118941581639170934384948965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158588775518894579179931953 118941581639170934384948965)
            ·
              refine ⟨22301546557344550197177931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118941581639170934384948965 22301546557344550197177931)
              ·
                refine ⟨33452319836016825295766897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22301546557344550197177931 33452319836016825295766897)
                ·
                  refine ⟨25089239877012618971825173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33452319836016825295766897 25089239877012618971825173)
                  ·
                    refine ⟨1176058119234966514304305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25089239877012618971825173 1176058119234966514304305)
                    ·
                      rfl

theorem cell23_6871095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_6871095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871095 prefixEnd_6871095 := by exact prefixLift 6871095
  have htrace : WordTrace (prefixWord ++ tailWord_6871095) baseStart_6871095 baseEnd_6871095 := by
    simpa [prefixWord, tailWord_6871095, baseEnd_6871095] using wordTrace_append hprefix tailTrace_6871095
  have hstable : (prefixWord ++ tailWord_6871095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871095).length < 2 ^ (prefixWord ++ tailWord_6871095).sum := by decide
  have hdescent : baseEnd_6871095 < baseStart_6871095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871096 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_6871096 : Nat := 118140960795 + 6871096 * 2 ^ 59
def prefixEnd_6871096 : Nat := 4983230072969 + 3 ^ 40 * 6871096 * 2
def baseEnd_6871096 : Nat := 3528174871185554039000411

theorem tailTrace_6871096 : CollatzResearch.WordTrace tailWord_6871096 prefixEnd_6871096 3528174871185554039000411 := by
  unfold tailWord_6871096
  simp only [CollatzResearch.WordTrace]
  refine ⟨125304729757600078307808571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167072973010133437743744761 125304729757600078307808571)
  ·
    refine ⟨187957094636400117461712857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125304729757600078307808571 187957094636400117461712857)
    ·
      refine ⟨140967820977300088096284643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187957094636400117461712857 140967820977300088096284643)
      ·
        refine ⟨211451731465950132144426965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140967820977300088096284643 211451731465950132144426965)
        ·
          refine ⟨4955899956233206222135007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 211451731465950132144426965 4955899956233206222135007)
          ·
            refine ⟨7433849934349809333202511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955899956233206222135007 7433849934349809333202511)
            ·
              refine ⟨11150774901524713999803767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433849934349809333202511 11150774901524713999803767)
              ·
                refine ⟨16726162352287070999705651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11150774901524713999803767 16726162352287070999705651)
                ·
                  refine ⟨25089243528430606499558477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16726162352287070999705651 25089243528430606499558477)
                  ·
                    refine ⟨9408466323161477437334429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25089243528430606499558477 9408466323161477437334429)
                    ·
                      refine ⟨3528174871185554039000411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9408466323161477437334429 3528174871185554039000411)
                      ·
                        rfl

theorem cell23_6871096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_6871096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871096 prefixEnd_6871096 := by exact prefixLift 6871096
  have htrace : WordTrace (prefixWord ++ tailWord_6871096) baseStart_6871096 baseEnd_6871096 := by
    simpa [prefixWord, tailWord_6871096, baseEnd_6871096] using wordTrace_append hprefix tailTrace_6871096
  have hstable : (prefixWord ++ tailWord_6871096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871096).length < 2 ^ (prefixWord ++ tailWord_6871096).sum := by decide
  have hdescent : baseEnd_6871096 < baseStart_6871096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871195 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_6871195 : Nat := 118140960795 + 6871195 * 2 ^ 59
def prefixEnd_6871195 : Nat := 4983230072969 + 3 ^ 40 * 6871195 * 2
def baseEnd_6871195 : Nat := 3528225705770349151662455

theorem tailTrace_6871195 : CollatzResearch.WordTrace tailWord_6871195 prefixEnd_6871195 3528225705770349151662455 := by
  unfold tailWord_6871195
  simp only [CollatzResearch.WordTrace]
  refine ⟨250613070341841496523471039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167075380227894331015647359 250613070341841496523471039)
  ·
    refine ⟨375919605512762244785206559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250613070341841496523471039 375919605512762244785206559)
    ·
      refine ⟨563879408269143367177809839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375919605512762244785206559 563879408269143367177809839)
      ·
        refine ⟨845819112403715050766714759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563879408269143367177809839 845819112403715050766714759)
        ·
          refine ⟨1268728668605572576150072139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845819112403715050766714759 1268728668605572576150072139)
          ·
            refine ⟨1903093002908358864225108209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268728668605572576150072139 1903093002908358864225108209)
            ·
              refine ⟨1427319752181269148168831157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903093002908358864225108209 1427319752181269148168831157)
              ·
                refine ⟨133811226766993982640827921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1427319752181269148168831157 133811226766993982640827921)
                ·
                  refine ⟨100358420075245486980620941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133811226766993982640827921 100358420075245486980620941)
                  ·
                    refine ⟨37634407528217057617732853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100358420075245486980620941 37634407528217057617732853)
                    ·
                      refine ⟨3528225705770349151662455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37634407528217057617732853 3528225705770349151662455)
                      ·
                        rfl

theorem cell23_6871195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_6871195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871195 prefixEnd_6871195 := by exact prefixLift 6871195
  have htrace : WordTrace (prefixWord ++ tailWord_6871195) baseStart_6871195 baseEnd_6871195 := by
    simpa [prefixWord, tailWord_6871195, baseEnd_6871195] using wordTrace_append hprefix tailTrace_6871195
  have hstable : (prefixWord ++ tailWord_6871195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871195).length < 2 ^ (prefixWord ++ tailWord_6871195).sum := by decide
  have hdescent : baseEnd_6871195 < baseStart_6871195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871215 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 10]
def baseStart_6871215 : Nat := 118140960795 + 6871215 * 2 ^ 59
def prefixEnd_6871215 : Nat := 4983230072969 + 3 ^ 40 * 6871215 * 2
def baseEnd_6871215 : Nat := 392026219487048785934707

theorem tailTrace_6871215 : CollatzResearch.WordTrace tailWord_6871215 prefixEnd_6871215 392026219487048785934707 := by
  unfold tailWord_6871215
  simp only [CollatzResearch.WordTrace]
  refine ⟨250613799801769039939199099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167075866534512693292799399 250613799801769039939199099)
  ·
    refine ⟨375920699702653559908798649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250613799801769039939199099 375920699702653559908798649)
    ·
      refine ⟨281940524776990169931598987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375920699702653559908798649 281940524776990169931598987)
      ·
        refine ⟨422910787165485254897398481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281940524776990169931598987 422910787165485254897398481)
        ·
          refine ⟨317183090374113941173048861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422910787165485254897398481 317183090374113941173048861)
          ·
            refine ⟨118943658890292727939893323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317183090374113941173048861 118943658890292727939893323)
            ·
              refine ⟨178415488335439091909839985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118943658890292727939893323 178415488335439091909839985)
              ·
                refine ⟨133811616251579318932379989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178415488335439091909839985 133811616251579318932379989)
                ·
                  refine ⟨392026219487048785934707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133811616251579318932379989 392026219487048785934707)
                  ·
                    rfl

theorem cell23_6871215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 10].length) (baseStart_6871215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871215 prefixEnd_6871215 := by exact prefixLift 6871215
  have htrace : WordTrace (prefixWord ++ tailWord_6871215) baseStart_6871215 baseEnd_6871215 := by
    simpa [prefixWord, tailWord_6871215, baseEnd_6871215] using wordTrace_append hprefix tailTrace_6871215
  have hstable : (prefixWord ++ tailWord_6871215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871215).length < 2 ^ (prefixWord ++ tailWord_6871215).sum := by decide
  have hdescent : baseEnd_6871215 < baseStart_6871215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871259 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 3]
def baseStart_6871259 : Nat := 118140960795 + 6871259 * 2 ^ 59
def prefixEnd_6871259 : Nat := 4983230072969 + 3 ^ 40 * 6871259 * 2
def baseEnd_6871259 : Nat := 3528258568532236901262161

theorem tailTrace_6871259 : CollatzResearch.WordTrace tailWord_6871259 prefixEnd_6871259 3528258568532236901262161 := by
  unfold tailWord_6871259
  simp only [CollatzResearch.WordTrace]
  refine ⟨250615404613609635453800831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167076936409073090302533887 250615404613609635453800831)
  ·
    refine ⟨375923106920414453180701247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250615404613609635453800831 375923106920414453180701247)
    ·
      refine ⟨563884660380621679771051871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375923106920414453180701247 563884660380621679771051871)
      ·
        refine ⟨845826990570932519656577807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563884660380621679771051871 845826990570932519656577807)
        ·
          refine ⟨1268740485856398779484866711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845826990570932519656577807 1268740485856398779484866711)
          ·
            refine ⟨1903110728784598169227300067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268740485856398779484866711 1903110728784598169227300067)
            ·
              refine ⟨2854666093176897253840950101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903110728784598169227300067 2854666093176897253840950101)
              ·
                refine ⟨16726559139708382346724317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2854666093176897253840950101 16726559139708382346724317)
                ·
                  refine ⟨6272459677390643380021619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16726559139708382346724317 6272459677390643380021619)
                  ·
                    refine ⟨9408689516085965070032429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6272459677390643380021619 9408689516085965070032429)
                    ·
                      refine ⟨3528258568532236901262161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9408689516085965070032429 3528258568532236901262161)
                      ·
                        rfl

theorem cell23_6871259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 3].length) (baseStart_6871259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871259 prefixEnd_6871259 := by exact prefixLift 6871259
  have htrace : WordTrace (prefixWord ++ tailWord_6871259) baseStart_6871259 baseEnd_6871259 := by
    simpa [prefixWord, tailWord_6871259, baseEnd_6871259] using wordTrace_append hprefix tailTrace_6871259
  have hstable : (prefixWord ++ tailWord_6871259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871259).length < 2 ^ (prefixWord ++ tailWord_6871259).sum := by decide
  have hdescent : baseEnd_6871259 < baseStart_6871259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871279 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 1, 5]
def baseStart_6871279 : Nat := 118140960795 + 6871279 * 2 ^ 59
def prefixEnd_6871279 : Nat := 4983230072969 + 3 ^ 40 * 6871279 * 2
def baseEnd_6871279 : Nat := 1176089612715108941004023

theorem tailTrace_6871279 : CollatzResearch.WordTrace tailWord_6871279 prefixEnd_6871279 1176089612715108941004023 := by
  unfold tailWord_6871279
  simp only [CollatzResearch.WordTrace]
  refine ⟨250616134073537178869528891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167077422715691452579685927 250616134073537178869528891)
  ·
    refine ⟨375924201110305768304293337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250616134073537178869528891 375924201110305768304293337)
    ·
      refine ⟨281943150832729326228220003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375924201110305768304293337 281943150832729326228220003)
      ·
        refine ⟨422914726249093989342330005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281943150832729326228220003 422914726249093989342330005)
        ·
          refine ⟨19824127792926280750421719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 422914726249093989342330005 19824127792926280750421719)
          ·
            refine ⟨29736191689389421125632579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19824127792926280750421719 29736191689389421125632579)
            ·
              refine ⟨44604287534084131688448869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29736191689389421125632579 44604287534084131688448869)
              ·
                refine ⟨8363303912640774691584163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44604287534084131688448869 8363303912640774691584163)
                ·
                  refine ⟨12544955868961162037376245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363303912640774691584163 12544955868961162037376245)
                  ·
                    refine ⟨1176089612715108941004023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12544955868961162037376245 1176089612715108941004023)
                    ·
                      rfl

theorem cell23_6871279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_6871279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871279 prefixEnd_6871279 := by exact prefixLift 6871279
  have htrace : WordTrace (prefixWord ++ tailWord_6871279) baseStart_6871279 baseEnd_6871279 := by
    simpa [prefixWord, tailWord_6871279, baseEnd_6871279] using wordTrace_append hprefix tailTrace_6871279
  have hstable : (prefixWord ++ tailWord_6871279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871279).length < 2 ^ (prefixWord ++ tailWord_6871279).sum := by decide
  have hdescent : baseEnd_6871279 < baseStart_6871279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871286 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6871286 : Nat := 118140960795 + 6871286 * 2 ^ 59
def prefixEnd_6871286 : Nat := 4983230072969 + 3 ^ 40 * 6871286 * 2
def baseEnd_6871286 : Nat := 3528272432509908295624537

theorem tailTrace_6871286 : CollatzResearch.WordTrace tailWord_6871286 prefixEnd_6871286 3528272432509908295624537 := by
  unfold tailWord_6871286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663524336531988691564607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167077592923007879376689141 15663524336531988691564607)
  ·
    refine ⟨23495286504797983037346911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15663524336531988691564607 23495286504797983037346911)
    ·
      refine ⟨35242929757196974556020367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23495286504797983037346911 35242929757196974556020367)
      ·
        refine ⟨52864394635795461834030551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35242929757196974556020367 52864394635795461834030551)
        ·
          refine ⟨79296591953693192751045827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52864394635795461834030551 79296591953693192751045827)
          ·
            refine ⟨118944887930539789126568741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79296591953693192751045827 118944887930539789126568741)
            ·
              refine ⟨22302166486976210461231639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118944887930539789126568741 22302166486976210461231639)
              ·
                refine ⟨33453249730464315691847459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22302166486976210461231639 33453249730464315691847459)
                ·
                  refine ⟨50179874595696473537771189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33453249730464315691847459 50179874595696473537771189)
                  ·
                    refine ⟨4704363243346544394166049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50179874595696473537771189 4704363243346544394166049)
                    ·
                      refine ⟨3528272432509908295624537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704363243346544394166049 3528272432509908295624537)
                      ·
                        rfl

theorem cell23_6871286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6871286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871286 prefixEnd_6871286 := by exact prefixLift 6871286
  have htrace : WordTrace (prefixWord ++ tailWord_6871286) baseStart_6871286 baseEnd_6871286 := by
    simpa [prefixWord, tailWord_6871286, baseEnd_6871286] using wordTrace_append hprefix tailTrace_6871286
  have hstable : (prefixWord ++ tailWord_6871286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871286).length < 2 ^ (prefixWord ++ tailWord_6871286).sum := by decide
  have hdescent : baseEnd_6871286 < baseStart_6871286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871299 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 4]
def baseStart_6871299 : Nat := 118140960795 + 6871299 * 2 ^ 59
def prefixEnd_6871299 : Nat := 4983230072969 + 3 ^ 40 * 6871299 * 2
def baseEnd_6871299 : Nat := 3528279107758416744761977

theorem tailTrace_6871299 : CollatzResearch.WordTrace tailWord_6871299 prefixEnd_6871299 3528279107758416744761977 := by
  unfold tailWord_6871299
  simp only [CollatzResearch.WordTrace]
  refine ⟨250616863533464722285256951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167077909022309814856837967 250616863533464722285256951)
  ·
    refine ⟨375925295300197083427885427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250616863533464722285256951 375925295300197083427885427)
    ·
      refine ⟨563887942950295625141828141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375925295300197083427885427 563887942950295625141828141)
      ·
        refine ⟨211457978606360859428185553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563887942950295625141828141 211457978606360859428185553)
        ·
          refine ⟨158593483954770644571139165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211457978606360859428185553 158593483954770644571139165)
          ·
            refine ⟨59472556483038991714177187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158593483954770644571139165 59472556483038991714177187)
            ·
              refine ⟨89208834724558487571265781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59472556483038991714177187 89208834724558487571265781)
              ·
                refine ⟨8363328255427358209806167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89208834724558487571265781 8363328255427358209806167)
                ·
                  refine ⟨12544992383141037314709251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363328255427358209806167 12544992383141037314709251)
                  ·
                    refine ⟨18817488574711555972063877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12544992383141037314709251 18817488574711555972063877)
                    ·
                      refine ⟨3528279107758416744761977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18817488574711555972063877 3528279107758416744761977)
                      ·
                        rfl

theorem cell23_6871299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_6871299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871299 prefixEnd_6871299 := by exact prefixLift 6871299
  have htrace : WordTrace (prefixWord ++ tailWord_6871299) baseStart_6871299 baseEnd_6871299 := by
    simpa [prefixWord, tailWord_6871299, baseEnd_6871299] using wordTrace_append hprefix tailTrace_6871299
  have hstable : (prefixWord ++ tailWord_6871299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871299).length < 2 ^ (prefixWord ++ tailWord_6871299).sum := by decide
  have hdescent : baseEnd_6871299 < baseStart_6871299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871310 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6871310 : Nat := 118140960795 + 6871310 * 2 ^ 59
def prefixEnd_6871310 : Nat := 4983230072969 + 3 ^ 40 * 6871310 * 2
def baseEnd_6871310 : Nat := 3528284756045616201724427

theorem tailTrace_6871310 : CollatzResearch.WordTrace tailWord_6871310 prefixEnd_6871310 3528284756045616201724427 := by
  unfold tailWord_6871310
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327158092053108895488423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167078176490949914109271589 31327158092053108895488423)
  ·
    refine ⟨46990737138079663343232635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31327158092053108895488423 46990737138079663343232635)
    ·
      refine ⟨70486105707119495014848953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46990737138079663343232635 70486105707119495014848953)
      ·
        refine ⟨52864579280339621261136715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70486105707119495014848953 52864579280339621261136715)
        ·
          refine ⟨79296868920509431891705073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52864579280339621261136715 79296868920509431891705073)
          ·
            refine ⟨59472651690382073918778805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79296868920509431891705073 59472651690382073918778805)
            ·
              refine ⟨5575561095973319429885513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59472651690382073918778805 5575561095973319429885513)
              ·
                refine ⟨4181670821979989572414135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575561095973319429885513 4181670821979989572414135)
                ·
                  refine ⟨6272506232969984358621203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181670821979989572414135 6272506232969984358621203)
                  ·
                    refine ⟨9408759349454976537931805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6272506232969984358621203 9408759349454976537931805)
                    ·
                      refine ⟨3528284756045616201724427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9408759349454976537931805 3528284756045616201724427)
                      ·
                        rfl

theorem cell23_6871310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6871310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871310 prefixEnd_6871310 := by exact prefixLift 6871310
  have htrace : WordTrace (prefixWord ++ tailWord_6871310) baseStart_6871310 baseEnd_6871310 := by
    simpa [prefixWord, tailWord_6871310, baseEnd_6871310] using wordTrace_append hprefix tailTrace_6871310
  have hstable : (prefixWord ++ tailWord_6871310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871310).length < 2 ^ (prefixWord ++ tailWord_6871310).sum := by decide
  have hdescent : baseEnd_6871310 < baseStart_6871310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871319 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6871319 : Nat := 118140960795 + 6871319 * 2 ^ 59
def prefixEnd_6871319 : Nat := 4983230072969 + 3 ^ 40 * 6871319 * 2
def baseEnd_6871319 : Nat := 3528289377371506666511885

theorem tailTrace_6871319 : CollatzResearch.WordTrace tailWord_6871319 prefixEnd_6871319 3528289377371506666511885 := by
  unfold tailWord_6871319
  simp only [CollatzResearch.WordTrace]
  refine ⟨250617592993392265700985011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167078395328928177133990007 250617592993392265700985011)
  ·
    refine ⟨375926389490088398551477517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250617592993392265700985011 375926389490088398551477517)
    ·
      refine ⟨140972396058783149456804069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375926389490088398551477517 140972396058783149456804069)
      ·
        refine ⟨26432324261021840523150763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140972396058783149456804069 26432324261021840523150763)
        ·
          refine ⟨39648486391532760784726145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26432324261021840523150763 39648486391532760784726145)
          ·
            refine ⟨29736364793649570588544609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39648486391532760784726145 29736364793649570588544609)
            ·
              refine ⟨22302273595237177941408457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29736364793649570588544609 22302273595237177941408457)
              ·
                refine ⟨16726705196427883456056343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22302273595237177941408457 16726705196427883456056343)
                ·
                  refine ⟨25090057794641825184084515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16726705196427883456056343 25090057794641825184084515)
                  ·
                    refine ⟨37635086691962737776126773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25090057794641825184084515 37635086691962737776126773)
                    ·
                      refine ⟨3528289377371506666511885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37635086691962737776126773 3528289377371506666511885)
                      ·
                        rfl

theorem cell23_6871319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6871319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871319 prefixEnd_6871319 := by exact prefixLift 6871319
  have htrace : WordTrace (prefixWord ++ tailWord_6871319) baseStart_6871319 baseEnd_6871319 := by
    simpa [prefixWord, tailWord_6871319, baseEnd_6871319] using wordTrace_append hprefix tailTrace_6871319
  have hstable : (prefixWord ++ tailWord_6871319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871319).length < 2 ^ (prefixWord ++ tailWord_6871319).sum := by decide
  have hdescent : baseEnd_6871319 < baseStart_6871319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871333 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_6871333 : Nat := 118140960795 + 6871333 * 2 ^ 59
def prefixEnd_6871333 : Nat := 4983230072969 + 3 ^ 40 * 6871333 * 2
def baseEnd_6871333 : Nat := 3528296566100669611736821

theorem tailTrace_6871333 : CollatzResearch.WordTrace tailWord_6871333 prefixEnd_6871333 3528296566100669611736821 := by
  unfold tailWord_6871333
  simp only [CollatzResearch.WordTrace]
  refine ⟨250618103615341546091994653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167078735743561030727996435 250618103615341546091994653)
  ·
    refine ⟨93981788855753079784497995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250618103615341546091994653 93981788855753079784497995)
    ·
      refine ⟨140972683283629619676746993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93981788855753079784497995 140972683283629619676746993)
      ·
        refine ⟨105729512462722214757560245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140972683283629619676746993 105729512462722214757560245)
        ·
          refine ⟨9912141793380207633521273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105729512462722214757560245 9912141793380207633521273)
          ·
            refine ⟨7434106345035155725140955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9912141793380207633521273 7434106345035155725140955)
            ·
              refine ⟨11151159517552733587711433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434106345035155725140955 11151159517552733587711433)
              ·
                refine ⟨8363369638164550190783575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11151159517552733587711433 8363369638164550190783575)
                ·
                  refine ⟨12545054457246825286175363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363369638164550190783575 12545054457246825286175363)
                  ·
                    refine ⟨18817581685870237929263045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12545054457246825286175363 18817581685870237929263045)
                    ·
                      refine ⟨3528296566100669611736821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18817581685870237929263045 3528296566100669611736821)
                      ·
                        rfl

theorem cell23_6871333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_6871333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871333 prefixEnd_6871333 := by exact prefixLift 6871333
  have htrace : WordTrace (prefixWord ++ tailWord_6871333) baseStart_6871333 baseEnd_6871333 := by
    simpa [prefixWord, tailWord_6871333, baseEnd_6871333] using wordTrace_append hprefix tailTrace_6871333
  have hstable : (prefixWord ++ tailWord_6871333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871333).length < 2 ^ (prefixWord ++ tailWord_6871333).sum := by decide
  have hdescent : baseEnd_6871333 < baseStart_6871333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871346 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_6871346 : Nat := 118140960795 + 6871346 * 2 ^ 59
def prefixEnd_6871346 : Nat := 4983230072969 + 3 ^ 40 * 6871346 * 2
def baseEnd_6871346 : Nat := 3528303241349178060874261

theorem tailTrace_6871346 : CollatzResearch.WordTrace tailWord_6871346 prefixEnd_6871346 3528303241349178060874261 := by
  unfold tailWord_6871346
  simp only [CollatzResearch.WordTrace]
  refine ⟨62654644441073612328054473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167079051842862966208145261 62654644441073612328054473)
  ·
    refine ⟨46990983330805209246040855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62654644441073612328054473 46990983330805209246040855)
    ·
      refine ⟨70486474996207813869061283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46990983330805209246040855 70486474996207813869061283)
      ·
        refine ⟨105729712494311720803591925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70486474996207813869061283 105729712494311720803591925)
        ·
          refine ⟨9912160546341723825336743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105729712494311720803591925 9912160546341723825336743)
          ·
            refine ⟨14868240819512585738005115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9912160546341723825336743 14868240819512585738005115)
            ·
              refine ⟨22302361229268878607007673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14868240819512585738005115 22302361229268878607007673)
              ·
                refine ⟨16726770921951658955255755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22302361229268878607007673 16726770921951658955255755)
                ·
                  refine ⟨25090156382927488432883633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16726770921951658955255755 25090156382927488432883633)
                  ·
                    refine ⟨18817617287195616324662725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25090156382927488432883633 18817617287195616324662725)
                    ·
                      refine ⟨3528303241349178060874261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18817617287195616324662725 3528303241349178060874261)
                      ·
                        rfl

theorem cell23_6871346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_6871346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871346 prefixEnd_6871346 := by exact prefixLift 6871346
  have htrace : WordTrace (prefixWord ++ tailWord_6871346) baseStart_6871346 baseEnd_6871346 := by
    simpa [prefixWord, tailWord_6871346, baseEnd_6871346] using wordTrace_append hprefix tailTrace_6871346
  have hstable : (prefixWord ++ tailWord_6871346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871346).length < 2 ^ (prefixWord ++ tailWord_6871346).sum := by decide
  have hdescent : baseEnd_6871346 < baseStart_6871346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871376 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2]
def baseStart_6871376 : Nat := 118140960795 + 6871376 * 2 ^ 59
def prefixEnd_6871376 : Nat := 4983230072969 + 3 ^ 40 * 6871376 * 2
def baseEnd_6871376 : Nat := 3528318645768812943499123

theorem tailTrace_6871376 : CollatzResearch.WordTrace tailWord_6871376 prefixEnd_6871376 3528318645768812943499123 := by
  unfold tailWord_6871376
  simp only [CollatzResearch.WordTrace]
  refine ⟨125309835977092882217904991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167079781302790509623873321 125309835977092882217904991)
  ·
    refine ⟨187964753965639323326857487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125309835977092882217904991 187964753965639323326857487)
    ·
      refine ⟨281947130948458984990286231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187964753965639323326857487 281947130948458984990286231)
      ·
        refine ⟨422920696422688477485429347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281947130948458984990286231 422920696422688477485429347)
        ·
          refine ⟨634381044634032716228144021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422920696422688477485429347 634381044634032716228144021)
          ·
            refine ⟨29736611467220283573194251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 634381044634032716228144021 29736611467220283573194251)
            ·
              refine ⟨44604917200830425359791377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29736611467220283573194251 44604917200830425359791377)
              ·
                refine ⟨33453687900622819019843533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44604917200830425359791377 33453687900622819019843533)
                ·
                  refine ⟨12545132962733557132441325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33453687900622819019843533 12545132962733557132441325)
                  ·
                    refine ⟨4704424861025083924665497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12545132962733557132441325 4704424861025083924665497)
                    ·
                      refine ⟨3528318645768812943499123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704424861025083924665497 3528318645768812943499123)
                      ·
                        rfl

theorem cell23_6871376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2].length) (baseStart_6871376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871376 prefixEnd_6871376 := by exact prefixLift 6871376
  have htrace : WordTrace (prefixWord ++ tailWord_6871376) baseStart_6871376 baseEnd_6871376 := by
    simpa [prefixWord, tailWord_6871376, baseEnd_6871376] using wordTrace_append hprefix tailTrace_6871376
  have hstable : (prefixWord ++ tailWord_6871376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871376).length < 2 ^ (prefixWord ++ tailWord_6871376).sum := by decide
  have hdescent : baseEnd_6871376 < baseStart_6871376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871410 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_6871410 : Nat := 118140960795 + 6871410 * 2 ^ 59
def prefixEnd_6871410 : Nat := 4983230072969 + 3 ^ 40 * 6871410 * 2
def baseEnd_6871410 : Nat := 3528336104111065810473967

theorem tailTrace_6871410 : CollatzResearch.WordTrace tailWord_6871410 prefixEnd_6871410 3528336104111065810473967 := by
  unfold tailWord_6871410
  simp only [CollatzResearch.WordTrace]
  refine ⟨62655228009015647060636921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167080608024041725495031789 62655228009015647060636921)
  ·
    refine ⟨46991421006761735295477691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62655228009015647060636921 46991421006761735295477691)
    ·
      refine ⟨70487131510142602943216537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46991421006761735295477691 70487131510142602943216537)
      ·
        refine ⟨52865348632606952207412403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70487131510142602943216537 52865348632606952207412403)
        ·
          refine ⟨79298022948910428311118605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52865348632606952207412403 79298022948910428311118605)
          ·
            refine ⟨29736758605841410616669477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79298022948910428311118605 29736758605841410616669477)
            ·
              refine ⟨5575642238595264490625527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29736758605841410616669477 5575642238595264490625527)
              ·
                refine ⟨8363463357892896735938291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575642238595264490625527 8363463357892896735938291)
                ·
                  refine ⟨12545195036839345103907437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363463357892896735938291 12545195036839345103907437)
                  ·
                    refine ⟨4704448138814754413965289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12545195036839345103907437 4704448138814754413965289)
                    ·
                      refine ⟨3528336104111065810473967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704448138814754413965289 3528336104111065810473967)
                      ·
                        rfl

theorem cell23_6871410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_6871410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871410 prefixEnd_6871410 := by exact prefixLift 6871410
  have htrace : WordTrace (prefixWord ++ tailWord_6871410) baseStart_6871410 baseEnd_6871410 := by
    simpa [prefixWord, tailWord_6871410, baseEnd_6871410] using wordTrace_append hprefix tailTrace_6871410
  have hstable : (prefixWord ++ tailWord_6871410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871410).length < 2 ^ (prefixWord ++ tailWord_6871410).sum := by decide
  have hdescent : baseEnd_6871410 < baseStart_6871410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871419 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_6871419 : Nat := 118140960795 + 6871419 * 2 ^ 59
def prefixEnd_6871419 : Nat := 4983230072969 + 3 ^ 40 * 6871419 * 2
def baseEnd_6871419 : Nat := 3528340725436956275261425

theorem tailTrace_6871419 : CollatzResearch.WordTrace tailWord_6871419 prefixEnd_6871419 3528340725436956275261425 := by
  unfold tailWord_6871419
  simp only [CollatzResearch.WordTrace]
  refine ⟨250621240293029982779625311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167080826862019988519750207 250621240293029982779625311)
  ·
    refine ⟨375931860439544974169437967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250621240293029982779625311 375931860439544974169437967)
    ·
      refine ⟨563897790659317461254156951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375931860439544974169437967 563897790659317461254156951)
      ·
        refine ⟨845846685988976191881235427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563897790659317461254156951 845846685988976191881235427)
        ·
          refine ⟨1268770028983464287821853141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845846685988976191881235427 1268770028983464287821853141)
          ·
            refine ⟨29736797554299944245824683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1268770028983464287821853141 29736797554299944245824683)
            ·
              refine ⟨44605196331449916368737025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29736797554299944245824683 44605196331449916368737025)
              ·
                refine ⟨33453897248587437276552769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44605196331449916368737025 33453897248587437276552769)
                ·
                  refine ⟨25090422936440577957414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33453897248587437276552769 25090422936440577957414577)
                  ·
                    refine ⟨18817817202330433468060933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25090422936440577957414577 18817817202330433468060933)
                    ·
                      refine ⟨3528340725436956275261425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18817817202330433468060933 3528340725436956275261425)
                      ·
                        rfl

theorem cell23_6871419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_6871419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871419 prefixEnd_6871419 := by exact prefixLift 6871419
  have htrace : WordTrace (prefixWord ++ tailWord_6871419) baseStart_6871419 baseEnd_6871419 := by
    simpa [prefixWord, tailWord_6871419, baseEnd_6871419] using wordTrace_append hprefix tailTrace_6871419
  have hstable : (prefixWord ++ tailWord_6871419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871419).length < 2 ^ (prefixWord ++ tailWord_6871419).sum := by decide
  have hdescent : baseEnd_6871419 < baseStart_6871419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871459 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 7]
def baseStart_6871459 : Nat := 118140960795 + 6871459 * 2 ^ 59
def prefixEnd_6871459 : Nat := 4983230072969 + 3 ^ 40 * 6871459 * 2
def baseEnd_6871459 : Nat := 1176120421554378706253747

theorem tailTrace_6871459 : CollatzResearch.WordTrace tailWord_6871459 prefixEnd_6871459 1176120421554378706253747 := by
  unfold tailWord_6871459
  simp only [CollatzResearch.WordTrace]
  refine ⟨250622699212885069611081431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167081799475256713074054287 250622699212885069611081431)
  ·
    refine ⟨375934048819327604416622147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250622699212885069611081431 375934048819327604416622147)
    ·
      refine ⟨563901073228991406624933221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375934048819327604416622147 563901073228991406624933221)
      ·
        refine ⟨105731451230435888742174979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 563901073228991406624933221 105731451230435888742174979)
        ·
          refine ⟨158597176845653833113262469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105731451230435888742174979 158597176845653833113262469)
          ·
            refine ⟨29736970658560093708736713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158597176845653833113262469 29736970658560093708736713)
            ·
              refine ⟨22302727993920070281552535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29736970658560093708736713 22302727993920070281552535)
              ·
                refine ⟨33454091990880105422328803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22302727993920070281552535 33454091990880105422328803)
                ·
                  refine ⟨50181137986320158133493205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33454091990880105422328803 50181137986320158133493205)
                  ·
                    refine ⟨1176120421554378706253747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50181137986320158133493205 1176120421554378706253747)
                    ·
                      rfl

theorem cell23_6871459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_6871459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871459 prefixEnd_6871459 := by exact prefixLift 6871459
  have htrace : WordTrace (prefixWord ++ tailWord_6871459) baseStart_6871459 baseEnd_6871459 := by
    simpa [prefixWord, tailWord_6871459, baseEnd_6871459] using wordTrace_append hprefix tailTrace_6871459
  have hstable : (prefixWord ++ tailWord_6871459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871459).length < 2 ^ (prefixWord ++ tailWord_6871459).sum := by decide
  have hdescent : baseEnd_6871459 < baseStart_6871459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871463 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 5]
def baseStart_6871463 : Nat := 118140960795 + 6871463 * 2 ^ 59
def prefixEnd_6871463 : Nat := 4983230072969 + 3 ^ 40 * 6871463 * 2
def baseEnd_6871463 : Nat := 392040368731750455901247

theorem tailTrace_6871463 : CollatzResearch.WordTrace tailWord_6871463 prefixEnd_6871463 392040368731750455901247 := by
  unfold tailWord_6871463
  simp only [CollatzResearch.WordTrace]
  refine ⟨250622845104870578294227043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167081896736580385529484695 250622845104870578294227043)
  ·
    refine ⟨375934267657305867441340565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250622845104870578294227043 375934267657305867441340565)
    ·
      refine ⟨17621918796436212536312839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 375934267657305867441340565 17621918796436212536312839)
      ·
        refine ⟨26432878194654318804469259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17621918796436212536312839 26432878194654318804469259)
        ·
          refine ⟨39649317291981478206703889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26432878194654318804469259 39649317291981478206703889)
          ·
            refine ⟨29736987968986108655027917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39649317291981478206703889 29736987968986108655027917)
            ·
              refine ⟨11151370488369790745635469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29736987968986108655027917 11151370488369790745635469)
              ·
                refine ⟨4181763933138671529613301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11151370488369790745635469 4181763933138671529613301)
                ·
                  refine ⟨392040368731750455901247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4181763933138671529613301 392040368731750455901247)
                  ·
                    rfl

theorem cell23_6871463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 5].length) (baseStart_6871463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871463 prefixEnd_6871463 := by exact prefixLift 6871463
  have htrace : WordTrace (prefixWord ++ tailWord_6871463) baseStart_6871463 baseEnd_6871463 := by
    simpa [prefixWord, tailWord_6871463, baseEnd_6871463] using wordTrace_append hprefix tailTrace_6871463
  have hstable : (prefixWord ++ tailWord_6871463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871463).length < 2 ^ (prefixWord ++ tailWord_6871463).sum := by decide
  have hdescent : baseEnd_6871463 < baseStart_6871463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871536 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 6]
def baseStart_6871536 : Nat := 118140960795 + 6871536 * 2 ^ 59
def prefixEnd_6871536 : Nat := 4983230072969 + 3 ^ 40 * 6871536 * 2
def baseEnd_6871536 : Nat := 392044533630392479722043

theorem tailTrace_6871536 : CollatzResearch.WordTrace tailWord_6871536 prefixEnd_6871536 392044533630392479722043 := by
  unfold tailWord_6871536
  simp only [CollatzResearch.WordTrace]
  refine ⟨125312753816803055880817231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167083671755737407841089641 125312753816803055880817231)
  ·
    refine ⟨187969130725204583821225847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125312753816803055880817231 187969130725204583821225847)
    ·
      refine ⟨281953696087806875731838771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187969130725204583821225847 281953696087806875731838771)
      ·
        refine ⟨422930544131710313597758157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281953696087806875731838771 422930544131710313597758157)
        ·
          refine ⟨158598954049391367599159309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422930544131710313597758157 158598954049391367599159309)
          ·
            refine ⟨59474607768521762849684741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158598954049391367599159309 59474607768521762849684741)
            ·
              refine ⟨11151488956597830534315889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59474607768521762849684741 11151488956597830534315889)
              ·
                refine ⟨8363616717448372900736917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11151488956597830534315889 8363616717448372900736917)
                ·
                  refine ⟨392044533630392479722043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8363616717448372900736917 392044533630392479722043)
                  ·
                    rfl

theorem cell23_6871536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_6871536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871536 prefixEnd_6871536 := by exact prefixLift 6871536
  have htrace : WordTrace (prefixWord ++ tailWord_6871536) baseStart_6871536 baseEnd_6871536 := by
    simpa [prefixWord, tailWord_6871536, baseEnd_6871536] using wordTrace_append hprefix tailTrace_6871536
  have hstable : (prefixWord ++ tailWord_6871536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871536).length < 2 ^ (prefixWord ++ tailWord_6871536).sum := by decide
  have hdescent : baseEnd_6871536 < baseStart_6871536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871539 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_6871539 : Nat := 118140960795 + 6871539 * 2 ^ 59
def prefixEnd_6871539 : Nat := 4983230072969 + 3 ^ 40 * 6871539 * 2
def baseEnd_6871539 : Nat := 3528402343115495805760873

theorem tailTrace_6871539 : CollatzResearch.WordTrace tailWord_6871539 prefixEnd_6871539 3528402343115495805760873 := by
  unfold tailWord_6871539
  simp only [CollatzResearch.WordTrace]
  refine ⟨250625617052595243273993671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167083744701730162182662447 250625617052595243273993671)
  ·
    refine ⟨375938425578892864910990507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250625617052595243273993671 375938425578892864910990507)
    ·
      refine ⟨563907638368339297366485761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375938425578892864910990507 563907638368339297366485761)
      ·
        refine ⟨422930728776254473024864321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563907638368339297366485761 422930728776254473024864321)
        ·
          refine ⟨317198046582190854768648241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422930728776254473024864321 317198046582190854768648241)
          ·
            refine ⟨237898534936643141076486181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317198046582190854768648241 237898534936643141076486181)
            ·
              refine ⟨44605975300620588951841159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237898534936643141076486181 44605975300620588951841159)
              ·
                refine ⟨66908962950930883427761739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44605975300620588951841159 66908962950930883427761739)
                ·
                  refine ⟨100363444426396325141642609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66908962950930883427761739 100363444426396325141642609)
                  ·
                    refine ⟨75272583319797243856231957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100363444426396325141642609 75272583319797243856231957)
                    ·
                      refine ⟨3528402343115495805760873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75272583319797243856231957 3528402343115495805760873)
                      ·
                        rfl

theorem cell23_6871539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_6871539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871539 prefixEnd_6871539 := by exact prefixLift 6871539
  have htrace : WordTrace (prefixWord ++ tailWord_6871539) baseStart_6871539 baseEnd_6871539 := by
    simpa [prefixWord, tailWord_6871539, baseEnd_6871539] using wordTrace_append hprefix tailTrace_6871539
  have hstable : (prefixWord ++ tailWord_6871539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871539).length < 2 ^ (prefixWord ++ tailWord_6871539).sum := by decide
  have hdescent : baseEnd_6871539 < baseStart_6871539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871563 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3]
def baseStart_6871563 : Nat := 118140960795 + 6871563 * 2 ^ 59
def prefixEnd_6871563 : Nat := 4983230072969 + 3 ^ 40 * 6871563 * 2
def baseEnd_6871563 : Nat := 3528414666651203711860763

theorem tailTrace_6871563 : CollatzResearch.WordTrace tailWord_6871563 prefixEnd_6871563 3528414666651203711860763 := by
  unfold tailWord_6871563
  simp only [CollatzResearch.WordTrace]
  refine ⟨250626492404508295372867343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167084328269672196915244895 250626492404508295372867343)
  ·
    refine ⟨375939738606762443059301015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250626492404508295372867343 375939738606762443059301015)
    ·
      refine ⟨563909607910143664588951523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375939738606762443059301015 563909607910143664588951523)
      ·
        refine ⟨845864411865215496883427285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563909607910143664588951523 845864411865215496883427285)
        ·
          refine ⟨19824947153090988208205327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 845864411865215496883427285 19824947153090988208205327)
          ·
            refine ⟨29737420729636482312307991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19824947153090988208205327 29737420729636482312307991)
            ·
              refine ⟨44606131094454723468461987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29737420729636482312307991 44606131094454723468461987)
              ·
                refine ⟨66909196641682085202692981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44606131094454723468461987 66909196641682085202692981)
                ·
                  refine ⟨6272737185157695487752467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66909196641682085202692981 6272737185157695487752467)
                  ·
                    refine ⟨9409105777736543231628701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6272737185157695487752467 9409105777736543231628701)
                    ·
                      refine ⟨3528414666651203711860763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409105777736543231628701 3528414666651203711860763)
                      ·
                        rfl

theorem cell23_6871563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3].length) (baseStart_6871563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871563 prefixEnd_6871563 := by exact prefixLift 6871563
  have htrace : WordTrace (prefixWord ++ tailWord_6871563) baseStart_6871563 baseEnd_6871563 := by
    simpa [prefixWord, tailWord_6871563, baseEnd_6871563] using wordTrace_append hprefix tailTrace_6871563
  have hstable : (prefixWord ++ tailWord_6871563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871563).length < 2 ^ (prefixWord ++ tailWord_6871563).sum := by decide
  have hdescent : baseEnd_6871563 < baseStart_6871563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871573 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_6871573 : Nat := 118140960795 + 6871573 * 2 ^ 59
def prefixEnd_6871573 : Nat := 4983230072969 + 3 ^ 40 * 6871573 * 2
def baseEnd_6871573 : Nat := 3528419801457748672735717

theorem tailTrace_6871573 : CollatzResearch.WordTrace tailWord_6871573 prefixEnd_6871573 3528419801457748672735717 := by
  unfold tailWord_6871573
  simp only [CollatzResearch.WordTrace]
  refine ⟨250626857134472067080731373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167084571422981378053820915 250626857134472067080731373)
  ·
    refine ⟨93985071425427025155274265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250626857134472067080731373 93985071425427025155274265)
    ·
      refine ⟨70488803569070268866455699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93985071425427025155274265 70488803569070268866455699)
      ·
        refine ⟨105733205353605403299683549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70488803569070268866455699 105733205353605403299683549)
        ·
          refine ⟨39649952007602026237381331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105733205353605403299683549 39649952007602026237381331)
          ·
            refine ⟨59474928011403039356071997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39649952007602026237381331 59474928011403039356071997)
            ·
              refine ⟨22303098004276139758526999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59474928011403039356071997 22303098004276139758526999)
              ·
                refine ⟨33454647006414209637790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22303098004276139758526999 33454647006414209637790499)
                ·
                  refine ⟨50181970509621314456685749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33454647006414209637790499 50181970509621314456685749)
                  ·
                    refine ⟨4704559735276998230314289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50181970509621314456685749 4704559735276998230314289)
                    ·
                      refine ⟨3528419801457748672735717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704559735276998230314289 3528419801457748672735717)
                      ·
                        rfl

theorem cell23_6871573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_6871573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871573 prefixEnd_6871573 := by exact prefixLift 6871573
  have htrace : WordTrace (prefixWord ++ tailWord_6871573) baseStart_6871573 baseEnd_6871573 := by
    simpa [prefixWord, tailWord_6871573, baseEnd_6871573] using wordTrace_append hprefix tailTrace_6871573
  have hstable : (prefixWord ++ tailWord_6871573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871573).length < 2 ^ (prefixWord ++ tailWord_6871573).sum := by decide
  have hdescent : baseEnd_6871573 < baseStart_6871573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871613 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_6871613 : Nat := 118140960795 + 6871613 * 2 ^ 59
def prefixEnd_6871613 : Nat := 4983230072969 + 3 ^ 40 * 6871613 * 2
def baseEnd_6871613 : Nat := 1176146780227976172078511

theorem tailTrace_6871613 : CollatzResearch.WordTrace tailWord_6871613 prefixEnd_6871613 1176146780227976172078511 := by
  unfold tailWord_6871613
  simp only [CollatzResearch.WordTrace]
  refine ⟨250628316054327153912187493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167085544036218102608124995 250628316054327153912187493)
  ·
    refine ⟨46992809260186341358535155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250628316054327153912187493 46992809260186341358535155)
    ·
      refine ⟨70489213890279512037802733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46992809260186341358535155 70489213890279512037802733)
      ·
        refine ⟨26433455208854817014176025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70489213890279512037802733 26433455208854817014176025)
        ·
          refine ⟨19825091406641112760632019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26433455208854817014176025 19825091406641112760632019)
          ·
            refine ⟨29737637109961669140948029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19825091406641112760632019 29737637109961669140948029)
            ·
              refine ⟨11151613916235625927855511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29737637109961669140948029 11151613916235625927855511)
              ·
                refine ⟨16727420874353438891783267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11151613916235625927855511 16727420874353438891783267)
                ·
                  refine ⟨25091131311530158337674901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16727420874353438891783267 25091131311530158337674901)
                  ·
                    refine ⟨1176146780227976172078511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25091131311530158337674901 1176146780227976172078511)
                    ·
                      rfl

theorem cell23_6871613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_6871613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871613 prefixEnd_6871613 := by exact prefixLift 6871613
  have htrace : WordTrace (prefixWord ++ tailWord_6871613) baseStart_6871613 baseEnd_6871613 := by
    simpa [prefixWord, tailWord_6871613, baseEnd_6871613] using wordTrace_append hprefix tailTrace_6871613
  have hstable : (prefixWord ++ tailWord_6871613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871613).length < 2 ^ (prefixWord ++ tailWord_6871613).sum := by decide
  have hdescent : baseEnd_6871613 < baseStart_6871613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871626 : List Nat := [3, 1, 2, 1, 1, 5, 1, 9]
def baseStart_6871626 : Nat := 118140960795 + 6871626 * 2 ^ 59
def prefixEnd_6871626 : Nat := 4983230072969 + 3 ^ 40 * 6871626 * 2
def baseEnd_6871626 : Nat := 130683222812312480198999

theorem tailTrace_6871626 : CollatzResearch.WordTrace tailWord_6871626 prefixEnd_6871626 130683222812312480198999 := by
  unfold tailWord_6871626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62657197550820014283102683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167085860135520038088273821 62657197550820014283102683)
  ·
    refine ⟨93985796326230021424654025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62657197550820014283102683 93985796326230021424654025)
    ·
      refine ⟨70489347244672516068490519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93985796326230021424654025 70489347244672516068490519)
      ·
        refine ⟨105734020867008774102735779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70489347244672516068490519 105734020867008774102735779)
        ·
          refine ⟨158601031300513161154103669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105734020867008774102735779 158601031300513161154103669)
          ·
            refine ⟨14868846684423108858197219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158601031300513161154103669 14868846684423108858197219)
            ·
              refine ⟨22303270026634663287295829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14868846684423108858197219 22303270026634663287295829)
              ·
                refine ⟨130683222812312480198999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22303270026634663287295829 130683222812312480198999)
                ·
                  rfl

theorem cell23_6871626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_6871626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871626 prefixEnd_6871626 := by exact prefixLift 6871626
  have htrace : WordTrace (prefixWord ++ tailWord_6871626) baseStart_6871626 baseEnd_6871626 := by
    simpa [prefixWord, tailWord_6871626, baseEnd_6871626] using wordTrace_append hprefix tailTrace_6871626
  have hstable : (prefixWord ++ tailWord_6871626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871626).length < 2 ^ (prefixWord ++ tailWord_6871626).sum := by decide
  have hdescent : baseEnd_6871626 < baseStart_6871626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871664 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 2, 4]
def baseStart_6871664 : Nat := 118140960795 + 6871664 * 2 ^ 59
def prefixEnd_6871664 : Nat := 4983230072969 + 3 ^ 40 * 6871664 * 2
def baseEnd_6871664 : Nat := 1176155509399102605565933

theorem tailTrace_6871664 : CollatzResearch.WordTrace tailWord_6871664 prefixEnd_6871664 1176155509399102605565933 := by
  unfold tailWord_6871664
  simp only [CollatzResearch.WordTrace]
  refine ⟨125315088088571194811147023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167086784118094926414862697 125315088088571194811147023)
  ·
    refine ⟨187972632132856792216720535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125315088088571194811147023 187972632132856792216720535)
    ·
      refine ⟨281958948199285188325080803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187972632132856792216720535 281958948199285188325080803)
      ·
        refine ⟨422938422298927782487621205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281958948199285188325080803 422938422298927782487621205)
        ·
          refine ⟨4956309636315559951026811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 422938422298927782487621205 4956309636315559951026811)
          ·
            refine ⟨7434464454473339926540217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956309636315559951026811 7434464454473339926540217)
            ·
              refine ⟨5575848340855004944905163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7434464454473339926540217 5575848340855004944905163)
              ·
                refine ⟨8363772511282507417357745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575848340855004944905163 8363772511282507417357745)
                ·
                  refine ⟨6272829383461880563018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8363772511282507417357745 6272829383461880563018309)
                  ·
                    refine ⟨1176155509399102605565933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272829383461880563018309 1176155509399102605565933)
                    ·
                      rfl

theorem cell23_6871664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_6871664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871664 prefixEnd_6871664 := by exact prefixLift 6871664
  have htrace : WordTrace (prefixWord ++ tailWord_6871664) baseStart_6871664 baseEnd_6871664 := by
    simpa [prefixWord, tailWord_6871664, baseEnd_6871664] using wordTrace_append hprefix tailTrace_6871664
  have hstable : (prefixWord ++ tailWord_6871664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871664).length < 2 ^ (prefixWord ++ tailWord_6871664).sum := by decide
  have hdescent : baseEnd_6871664 < baseStart_6871664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871680 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2]
def baseStart_6871680 : Nat := 118140960795 + 6871680 * 2 ^ 59
def prefixEnd_6871680 : Nat := 4983230072969 + 3 ^ 40 * 6871680 * 2
def baseEnd_6871680 : Nat := 3528474743887779754097725

theorem tailTrace_6871680 : CollatzResearch.WordTrace tailWord_6871680 prefixEnd_6871680 3528474743887779754097725 := by
  unfold tailWord_6871680
  simp only [CollatzResearch.WordTrace]
  refine ⟨125315379872542212177438247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167087173163389616236584329 125315379872542212177438247)
  ·
    refine ⟨187973069808813318266157371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125315379872542212177438247 187973069808813318266157371)
    ·
      refine ⟨281959604713219977399236057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187973069808813318266157371 281959604713219977399236057)
      ·
        refine ⟨211469703534914983049427043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281959604713219977399236057 211469703534914983049427043)
        ·
          refine ⟨317204555302372474574140565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211469703534914983049427043 317204555302372474574140565)
          ·
            refine ⟨14868963529798709745662839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317204555302372474574140565 14868963529798709745662839)
            ·
              refine ⟨22303445294698064618494259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14868963529798709745662839 22303445294698064618494259)
              ·
                refine ⟨33455167942047096927741389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22303445294698064618494259 33455167942047096927741389)
                ·
                  refine ⟨12545687978267661347903021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33455167942047096927741389 12545687978267661347903021)
                  ·
                    refine ⟨4704632991850373005463633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12545687978267661347903021 4704632991850373005463633)
                    ·
                      refine ⟨3528474743887779754097725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704632991850373005463633 3528474743887779754097725)
                      ·
                        rfl

theorem cell23_6871680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_6871680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871680 prefixEnd_6871680 := by exact prefixLift 6871680
  have htrace : WordTrace (prefixWord ++ tailWord_6871680) baseStart_6871680 baseEnd_6871680 := by
    simpa [prefixWord, tailWord_6871680, baseEnd_6871680] using wordTrace_append hprefix tailTrace_6871680
  have hstable : (prefixWord ++ tailWord_6871680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871680).length < 2 ^ (prefixWord ++ tailWord_6871680).sum := by decide
  have hdescent : baseEnd_6871680 < baseStart_6871680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871727 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 2, 2, 2]
def baseStart_6871727 : Nat := 118140960795 + 6871727 * 2 ^ 59
def prefixEnd_6871727 : Nat := 4983230072969 + 3 ^ 40 * 6871727 * 2
def baseEnd_6871727 : Nat := 3528498877478541070210009

theorem tailTrace_6871727 : CollatzResearch.WordTrace tailWord_6871727 prefixEnd_6871727 3528498877478541070210009 := by
  unfold tailWord_6871727
  simp only [CollatzResearch.WordTrace]
  refine ⟨250632473975914151381837435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167088315983942767587891623 250632473975914151381837435)
  ·
    refine ⟨375948710963871227072756153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250632473975914151381837435 375948710963871227072756153)
    ·
      refine ⟨281961533222903420304567115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375948710963871227072756153 281961533222903420304567115)
      ·
        refine ⟨422942299834355130456850673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281961533222903420304567115 422942299834355130456850673)
        ·
          refine ⟨317206724875766347842638005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422942299834355130456850673 317206724875766347842638005)
          ·
            refine ⟨29738130457103095110247313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317206724875766347842638005 29738130457103095110247313)
            ·
              refine ⟨22303597842827321332685485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29738130457103095110247313 22303597842827321332685485)
              ·
                refine ⟨8363849191060245499757057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22303597842827321332685485 8363849191060245499757057)
                ·
                  refine ⟨6272886893295184124817793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8363849191060245499757057 6272886893295184124817793)
                  ·
                    refine ⟨4704665169971388093613345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6272886893295184124817793 4704665169971388093613345)
                    ·
                      refine ⟨3528498877478541070210009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704665169971388093613345 3528498877478541070210009)
                      ·
                        rfl

theorem cell23_6871727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2, 2].length) (baseStart_6871727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871727 prefixEnd_6871727 := by exact prefixLift 6871727
  have htrace : WordTrace (prefixWord ++ tailWord_6871727) baseStart_6871727 baseEnd_6871727 := by
    simpa [prefixWord, tailWord_6871727, baseEnd_6871727] using wordTrace_append hprefix tailTrace_6871727
  have hstable : (prefixWord ++ tailWord_6871727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871727).length < 2 ^ (prefixWord ++ tailWord_6871727).sum := by decide
  have hdescent : baseEnd_6871727 < baseStart_6871727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871733 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 9]
def baseStart_6871733 : Nat := 118140960795 + 6871733 * 2 ^ 59
def prefixEnd_6871733 : Nat := 4983230072969 + 3 ^ 40 * 6871733 * 2
def baseEnd_6871733 : Nat := 392055773151385338526109

theorem tailTrace_6871733 : CollatzResearch.WordTrace tailWord_6871733 prefixEnd_6871733 392055773151385338526109 := by
  unfold tailWord_6871733
  simp only [CollatzResearch.WordTrace]
  refine ⟨250632692813892414406555853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167088461875928276271037235 250632692813892414406555853)
  ·
    refine ⟨93987259805209655402458445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250632692813892414406555853 93987259805209655402458445)
    ·
      refine ⟨35245222426953620775921917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93987259805209655402458445 35245222426953620775921917)
      ·
        refine ⟨13216958410107607790970719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35245222426953620775921917 13216958410107607790970719)
        ·
          refine ⟨19825437615161411686456079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13216958410107607790970719 19825437615161411686456079)
          ·
            refine ⟨29738156422742117529684119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19825437615161411686456079 29738156422742117529684119)
            ·
              refine ⟨44607234634113176294526179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29738156422742117529684119 44607234634113176294526179)
              ·
                refine ⟨66910851951169764441789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44607234634113176294526179 66910851951169764441789269)
                ·
                  refine ⟨392055773151385338526109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66910851951169764441789269 392055773151385338526109)
                  ·
                    rfl

theorem cell23_6871733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_6871733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871733 prefixEnd_6871733 := by exact prefixLift 6871733
  have htrace : WordTrace (prefixWord ++ tailWord_6871733) baseStart_6871733 baseEnd_6871733 := by
    simpa [prefixWord, tailWord_6871733, baseEnd_6871733] using wordTrace_append hprefix tailTrace_6871733
  have hstable : (prefixWord ++ tailWord_6871733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871733).length < 2 ^ (prefixWord ++ tailWord_6871733).sum := by decide
  have hdescent : baseEnd_6871733 < baseStart_6871733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871823 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 6]
def baseStart_6871823 : Nat := 118140960795 + 6871823 * 2 ^ 59
def prefixEnd_6871823 : Nat := 4983230072969 + 3 ^ 40 * 6871823 * 2
def baseEnd_6871823 : Nat := 392060907957930299401063

theorem tailTrace_6871823 : CollatzResearch.WordTrace tailWord_6871823 prefixEnd_6871823 392060907957930299401063 := by
  unfold tailWord_6871823
  simp only [CollatzResearch.WordTrace]
  refine ⟨250635975383566359777332123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167090650255710906518221415 250635975383566359777332123)
  ·
    refine ⟨375953963075349539665998185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250635975383566359777332123 375953963075349539665998185)
    ·
      refine ⟨281965472306512154749498639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375953963075349539665998185 281965472306512154749498639)
      ·
        refine ⟨422948208459768232124247959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281965472306512154749498639 422948208459768232124247959)
        ·
          refine ⟨634422312689652348186371939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422948208459768232124247959 634422312689652348186371939)
          ·
            refine ⟨951633469034478522279557909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634422312689652348186371939 951633469034478522279557909)
            ·
              refine ⟨44607818860991180731854277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 951633469034478522279557909 44607818860991180731854277)
              ·
                refine ⟨8363966036435846387222677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44607818860991180731854277 8363966036435846387222677)
                ·
                  refine ⟨392060907957930299401063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8363966036435846387222677 392060907957930299401063)
                  ·
                    rfl

theorem cell23_6871823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 6].length) (baseStart_6871823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871823 prefixEnd_6871823 := by exact prefixLift 6871823
  have htrace : WordTrace (prefixWord ++ tailWord_6871823) baseStart_6871823 baseEnd_6871823 := by
    simpa [prefixWord, tailWord_6871823, baseEnd_6871823] using wordTrace_append hprefix tailTrace_6871823
  have hstable : (prefixWord ++ tailWord_6871823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871823).length < 2 ^ (prefixWord ++ tailWord_6871823).sum := by decide
  have hdescent : baseEnd_6871823 < baseStart_6871823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871833 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_6871833 : Nat := 118140960795 + 6871833 * 2 ^ 59
def prefixEnd_6871833 : Nat := 4983230072969 + 3 ^ 40 * 6871833 * 2
def baseEnd_6871833 : Nat := 3528553306427917655484521

theorem tailTrace_6871833 : CollatzResearch.WordTrace tailWord_6871833 prefixEnd_6871833 3528553306427917655484521 := by
  unfold tailWord_6871833
  simp only [CollatzResearch.WordTrace]
  refine ⟨250636340113530131485196153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167090893409020087656797435 250636340113530131485196153)
  ·
    refine ⟨187977255085147598613897115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250636340113530131485196153 187977255085147598613897115)
    ·
      refine ⟨281965882627721397920845673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187977255085147598613897115 281965882627721397920845673)
      ·
        refine ⟨211474411970791048440634255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281965882627721397920845673 211474411970791048440634255)
        ·
          refine ⟨317211617956186572660951383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211474411970791048440634255 317211617956186572660951383)
          ·
            refine ⟨475817426934279858991427075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317211617956186572660951383 475817426934279858991427075)
            ·
              refine ⟨713726140401419788487140613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475817426934279858991427075 713726140401419788487140613)
              ·
                refine ⟨133823651325266210341338865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713726140401419788487140613 133823651325266210341338865)
                ·
                  refine ⟨100367738493949657756004149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133823651325266210341338865 100367738493949657756004149)
                  ·
                    refine ⟨9409475483807780414625389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100367738493949657756004149 9409475483807780414625389)
                    ·
                      refine ⟨3528553306427917655484521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409475483807780414625389 3528553306427917655484521)
                      ·
                        rfl

theorem cell23_6871833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_6871833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871833 prefixEnd_6871833 := by exact prefixLift 6871833
  have htrace : WordTrace (prefixWord ++ tailWord_6871833) baseStart_6871833 baseEnd_6871833 := by
    simpa [prefixWord, tailWord_6871833, baseEnd_6871833] using wordTrace_append hprefix tailTrace_6871833
  have hstable : (prefixWord ++ tailWord_6871833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871833).length < 2 ^ (prefixWord ++ tailWord_6871833).sum := by decide
  have hdescent : baseEnd_6871833 < baseStart_6871833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871840 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 6]
def baseStart_6871840 : Nat := 118140960795 + 6871840 * 2 ^ 59
def prefixEnd_6871840 : Nat := 4983230072969 + 3 ^ 40 * 6871840 * 2
def baseEnd_6871840 : Nat := 392061877865833236455221

theorem tailTrace_6871840 : CollatzResearch.WordTrace tailWord_6871840 prefixEnd_6871840 392061877865833236455221 := by
  unfold tailWord_6871840
  simp only [CollatzResearch.WordTrace]
  refine ⟨125318297712252385840350487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167091063616336514453800649 125318297712252385840350487)
  ·
    refine ⟨187977446568378578760525731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125318297712252385840350487 187977446568378578760525731)
    ·
      refine ⟨281966169852567868140788597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187977446568378578760525731 281966169852567868140788597)
      ·
        refine ⟨26434328423678237638198931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281966169852567868140788597 26434328423678237638198931)
        ·
          refine ⟨39651492635517356457298397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26434328423678237638198931 39651492635517356457298397)
          ·
            refine ⟨14869309738319008671486899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39651492635517356457298397 14869309738319008671486899)
            ·
              refine ⟨22303964607478513007230349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14869309738319008671486899 22303964607478513007230349)
              ·
                refine ⟨8363986727804442377711381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22303964607478513007230349 8363986727804442377711381)
                ·
                  refine ⟨392061877865833236455221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8363986727804442377711381 392061877865833236455221)
                  ·
                    rfl

theorem cell23_6871840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_6871840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871840 prefixEnd_6871840 := by exact prefixLift 6871840
  have htrace : WordTrace (prefixWord ++ tailWord_6871840) baseStart_6871840 baseEnd_6871840 := by
    simpa [prefixWord, tailWord_6871840, baseEnd_6871840] using wordTrace_append hprefix tailTrace_6871840
  have hstable : (prefixWord ++ tailWord_6871840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871840).length < 2 ^ (prefixWord ++ tailWord_6871840).sum := by decide
  have hdescent : baseEnd_6871840 < baseStart_6871840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871854 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6871854 : Nat := 118140960795 + 6871854 * 2 ^ 59
def prefixEnd_6871854 : Nat := 4983230072969 + 3 ^ 40 * 6871854 * 2
def baseEnd_6871854 : Nat := 3528564089521662073321925

theorem tailTrace_6871854 : CollatzResearch.WordTrace tailWord_6871854 prefixEnd_6871854 3528564089521662073321925 := by
  unfold tailWord_6871854
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329638255806756508963827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167091404030969368047807077 31329638255806756508963827)
  ·
    refine ⟨46994457383710134763445741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31329638255806756508963827 46994457383710134763445741)
    ·
      refine ⟨17622921518891300536292153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46994457383710134763445741 17622921518891300536292153)
      ·
        refine ⟨13217191139168475402219115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17622921518891300536292153 13217191139168475402219115)
        ·
          refine ⟨19825786708752713103328673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217191139168475402219115 19825786708752713103328673)
          ·
            refine ⟨14869340031564534827496505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19825786708752713103328673 14869340031564534827496505)
            ·
              refine ⟨11152005023673401120622379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14869340031564534827496505 11152005023673401120622379)
              ·
                refine ⟨16728007535510101680933569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152005023673401120622379 16728007535510101680933569)
                ·
                  refine ⟨12546005651632576260700177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16728007535510101680933569 12546005651632576260700177)
                  ·
                    refine ⟨9409504238724432195525133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12546005651632576260700177 9409504238724432195525133)
                    ·
                      refine ⟨3528564089521662073321925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409504238724432195525133 3528564089521662073321925)
                      ·
                        rfl

theorem cell23_6871854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6871854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871854 prefixEnd_6871854 := by exact prefixLift 6871854
  have htrace : WordTrace (prefixWord ++ tailWord_6871854) baseStart_6871854 baseEnd_6871854 := by
    simpa [prefixWord, tailWord_6871854, baseEnd_6871854] using wordTrace_append hprefix tailTrace_6871854
  have hstable : (prefixWord ++ tailWord_6871854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871854).length < 2 ^ (prefixWord ++ tailWord_6871854).sum := by decide
  have hdescent : baseEnd_6871854 < baseStart_6871854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871878 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_6871878 : Nat := 118140960795 + 6871878 * 2 ^ 59
def prefixEnd_6871878 : Nat := 4983230072969 + 3 ^ 40 * 6871878 * 2
def baseEnd_6871878 : Nat := 1176192137685789993140605

theorem tailTrace_6871878 : CollatzResearch.WordTrace tailWord_6871878 prefixEnd_6871878 1176192137685789993140605 := by
  unfold tailWord_6871878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832436918698972005330759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167091987598911402780389525 7832436918698972005330759)
  ·
    refine ⟨11748655378048458007996139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7832436918698972005330759 11748655378048458007996139)
    ·
      refine ⟨17622983067072687011994209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11748655378048458007996139 17622983067072687011994209)
      ·
        refine ⟨13217237300304515258995657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17622983067072687011994209 13217237300304515258995657)
        ·
          refine ⟨9912927975228386444246743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13217237300304515258995657 9912927975228386444246743)
          ·
            refine ⟨14869391962842579666370115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9912927975228386444246743 14869391962842579666370115)
            ·
              refine ⟨22304087944263869499555173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14869391962842579666370115 22304087944263869499555173)
              ·
                refine ⟨4182016489549475531166595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22304087944263869499555173 4182016489549475531166595)
                ·
                  refine ⟨6273024734324213296749893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182016489549475531166595 6273024734324213296749893)
                  ·
                    refine ⟨1176192137685789993140605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273024734324213296749893 1176192137685789993140605)
                    ·
                      rfl

theorem cell23_6871878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_6871878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871878 prefixEnd_6871878 := by exact prefixLift 6871878
  have htrace : WordTrace (prefixWord ++ tailWord_6871878) baseStart_6871878 baseEnd_6871878 := by
    simpa [prefixWord, tailWord_6871878, baseEnd_6871878] using wordTrace_append hprefix tailTrace_6871878
  have hstable : (prefixWord ++ tailWord_6871878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871878).length < 2 ^ (prefixWord ++ tailWord_6871878).sum := by decide
  have hdescent : baseEnd_6871878 < baseStart_6871878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871890 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_6871890 : Nat := 118140960795 + 6871890 * 2 ^ 59
def prefixEnd_6871890 : Nat := 4983230072969 + 3 ^ 40 * 6871890 * 2
def baseEnd_6871890 : Nat := 3528582574825223932471759

theorem tailTrace_6871890 : CollatzResearch.WordTrace tailWord_6871890 prefixEnd_6871890 3528582574825223932471759 := by
  unfold tailWord_6871890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62659604768580907555005281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167092279382882420146680749 62659604768580907555005281)
  ·
    refine ⟨46994703576435680666253961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62659604768580907555005281 46994703576435680666253961)
    ·
      refine ⟨35246027682326760499690471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46994703576435680666253961 35246027682326760499690471)
      ·
        refine ⟨52869041523490140749535707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35246027682326760499690471 52869041523490140749535707)
        ·
          refine ⟨79303562285235211124303561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52869041523490140749535707 79303562285235211124303561)
          ·
            refine ⟨59477671713926408343227671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79303562285235211124303561 59477671713926408343227671)
            ·
              refine ⟨89216507570889612514841507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59477671713926408343227671 89216507570889612514841507)
              ·
                refine ⟨133824761356334418772262261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89216507570889612514841507 133824761356334418772262261)
                ·
                  refine ⟨12546071377156351759899587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133824761356334418772262261 12546071377156351759899587)
                  ·
                    refine ⟨18819107065734527639849381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12546071377156351759899587 18819107065734527639849381)
                    ·
                      refine ⟨3528582574825223932471759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18819107065734527639849381 3528582574825223932471759)
                      ·
                        rfl

theorem cell23_6871890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_6871890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871890 prefixEnd_6871890 := by exact prefixLift 6871890
  have htrace : WordTrace (prefixWord ++ tailWord_6871890) baseStart_6871890 baseEnd_6871890 := by
    simpa [prefixWord, tailWord_6871890, baseEnd_6871890] using wordTrace_append hprefix tailTrace_6871890
  have hstable : (prefixWord ++ tailWord_6871890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871890).length < 2 ^ (prefixWord ++ tailWord_6871890).sum := by decide
  have hdescent : baseEnd_6871890 < baseStart_6871890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871918 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6871918 : Nat := 118140960795 + 6871918 * 2 ^ 59
def prefixEnd_6871918 : Nat := 4983230072969 + 3 ^ 40 * 6871918 * 2
def baseEnd_6871918 : Nat := 3528596952283549822921631

theorem tailTrace_6871918 : CollatzResearch.WordTrace tailWord_6871918 prefixEnd_6871918 3528596952283549822921631 := by
  unfold tailWord_6871918
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329930039777773875255051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167092960212148127334693605 31329930039777773875255051)
  ·
    refine ⟨46994895059666660812882577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31329930039777773875255051 46994895059666660812882577)
    ·
      refine ⟨35246171294749995609661933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46994895059666660812882577 35246171294749995609661933)
      ·
        refine ⟨13217314235531248353623225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35246171294749995609661933 13217314235531248353623225)
        ·
          refine ⟨9912985676648436265217419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13217314235531248353623225 9912985676648436265217419)
          ·
            refine ⟨14869478514972654397826129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9912985676648436265217419 14869478514972654397826129)
            ·
              refine ⟨11152108886229490798369597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14869478514972654397826129 11152108886229490798369597)
              ·
                refine ⟨4182040832336059049388599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11152108886229490798369597 4182040832336059049388599)
                ·
                  refine ⟨6273061248504088574082899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182040832336059049388599 6273061248504088574082899)
                  ·
                    refine ⟨9409591872756132861124349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273061248504088574082899 9409591872756132861124349)
                    ·
                      refine ⟨3528596952283549822921631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409591872756132861124349 3528596952283549822921631)
                      ·
                        rfl

theorem cell23_6871918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6871918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871918 prefixEnd_6871918 := by exact prefixLift 6871918
  have htrace : WordTrace (prefixWord ++ tailWord_6871918) baseStart_6871918 baseEnd_6871918 := by
    simpa [prefixWord, tailWord_6871918, baseEnd_6871918] using wordTrace_append hprefix tailTrace_6871918
  have hstable : (prefixWord ++ tailWord_6871918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871918).length < 2 ^ (prefixWord ++ tailWord_6871918).sum := by decide
  have hdescent : baseEnd_6871918 < baseStart_6871918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871920 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_6871920 : Nat := 118140960795 + 6871920 * 2 ^ 59
def prefixEnd_6871920 : Nat := 4983230072969 + 3 ^ 40 * 6871920 * 2
def baseEnd_6871920 : Nat := 3528597979244858815096621

theorem tailTrace_6871920 : CollatzResearch.WordTrace tailWord_6871920 prefixEnd_6871920 3528597979244858815096621 := by
  unfold tailWord_6871920
  simp only [CollatzResearch.WordTrace]
  refine ⟨125319756632107472671806607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167093008842809963562408809 125319756632107472671806607)
  ·
    refine ⟨187979634948161209007709911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125319756632107472671806607 187979634948161209007709911)
    ·
      refine ⟨281969452422241813511564867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187979634948161209007709911 281969452422241813511564867)
      ·
        refine ⟨422954178633362720267347301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281969452422241813511564867 422954178633362720267347301)
        ·
          refine ⟨79303908493755510050127619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422954178633362720267347301 79303908493755510050127619)
          ·
            refine ⟨118955862740633265075191429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79303908493755510050127619 118955862740633265075191429)
            ·
              refine ⟨22304224263868737201598393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118955862740633265075191429 22304224263868737201598393)
              ·
                refine ⟨16728168197901552901198795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22304224263868737201598393 16728168197901552901198795)
                ·
                  refine ⟨25092252296852329351798193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16728168197901552901198795 25092252296852329351798193)
                  ·
                    refine ⟨18819189222639247013848645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25092252296852329351798193 18819189222639247013848645)
                    ·
                      refine ⟨3528597979244858815096621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18819189222639247013848645 3528597979244858815096621)
                      ·
                        rfl

theorem cell23_6871920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_6871920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871920 prefixEnd_6871920 := by exact prefixLift 6871920
  have htrace : WordTrace (prefixWord ++ tailWord_6871920) baseStart_6871920 baseEnd_6871920 := by
    simpa [prefixWord, tailWord_6871920, baseEnd_6871920] using wordTrace_append hprefix tailTrace_6871920
  have hstable : (prefixWord ++ tailWord_6871920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871920).length < 2 ^ (prefixWord ++ tailWord_6871920).sum := by decide
  have hdescent : baseEnd_6871920 < baseStart_6871920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871941 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 1, 2, 2]
def baseStart_6871941 : Nat := 118140960795 + 6871941 * 2 ^ 59
def prefixEnd_6871941 : Nat := 4983230072969 + 3 ^ 40 * 6871941 * 2
def baseEnd_6871941 : Nat := 3528608762338603232934025

theorem tailTrace_6871941 : CollatzResearch.WordTrace tailWord_6871941 prefixEnd_6871941 3528608762338603232934025 := by
  unfold tailWord_6871941
  simp only [CollatzResearch.WordTrace]
  refine ⟨250640279197138865930127677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167093519464759243953418451 250640279197138865930127677)
  ·
    refine ⟨93990104698927074723797879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250640279197138865930127677 93990104698927074723797879)
    ·
      refine ⟨140985157048390612085696819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93990104698927074723797879 140985157048390612085696819)
      ·
        refine ⟨211477735572585918128545229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140985157048390612085696819 211477735572585918128545229)
        ·
          refine ⟨79304150839719719298204461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211477735572585918128545229 79304150839719719298204461)
          ·
            refine ⟨29739056564894894736826673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79304150839719719298204461 29739056564894894736826673)
            ·
              refine ⟨22304292423671171052620005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29739056564894894736826673 22304292423671171052620005)
              ·
                refine ⟨4182054829438344572366251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22304292423671171052620005 4182054829438344572366251)
                ·
                  refine ⟨6273082244157516858549377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182054829438344572366251 6273082244157516858549377)
                  ·
                    refine ⟨4704811683118137643912033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273082244157516858549377 4704811683118137643912033)
                    ·
                      refine ⟨3528608762338603232934025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704811683118137643912033 3528608762338603232934025)
                      ·
                        rfl

theorem cell23_6871941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_6871941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871941 prefixEnd_6871941 := by exact prefixLift 6871941
  have htrace : WordTrace (prefixWord ++ tailWord_6871941) baseStart_6871941 baseEnd_6871941 := by
    simpa [prefixWord, tailWord_6871941, baseEnd_6871941] using wordTrace_append hprefix tailTrace_6871941
  have hstable : (prefixWord ++ tailWord_6871941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871941).length < 2 ^ (prefixWord ++ tailWord_6871941).sum := by decide
  have hdescent : baseEnd_6871941 < baseStart_6871941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871957 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_6871957 : Nat := 118140960795 + 6871957 * 2 ^ 59
def prefixEnd_6871957 : Nat := 4983230072969 + 3 ^ 40 * 6871957 * 2
def baseEnd_6871957 : Nat := 3528616978029075170333951

theorem tailTrace_6871957 : CollatzResearch.WordTrace tailWord_6871957 prefixEnd_6871957 3528616978029075170333951 := by
  unfold tailWord_6871957
  simp only [CollatzResearch.WordTrace]
  refine ⟨250640862765080900662710125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167093908510053933775140083 250640862765080900662710125)
  ·
    refine ⟨93990323536905337748516297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250640862765080900662710125 93990323536905337748516297)
    ·
      refine ⟨70492742652679003311387223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93990323536905337748516297 70492742652679003311387223)
      ·
        refine ⟨105739113979018504967080835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70492742652679003311387223 105739113979018504967080835)
        ·
          refine ⟨158608670968527757450621253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105739113979018504967080835 158608670968527757450621253)
          ·
            refine ⟨29739125806598954521991485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158608670968527757450621253 29739125806598954521991485)
            ·
              refine ⟨11152172177474607945746807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29739125806598954521991485 11152172177474607945746807)
              ·
                refine ⟨16728258266211911918620211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152172177474607945746807 16728258266211911918620211)
                ·
                  refine ⟨25092387399317867877930317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16728258266211911918620211 25092387399317867877930317)
                  ·
                    refine ⟨9409645274744200454223869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25092387399317867877930317 9409645274744200454223869)
                    ·
                      refine ⟨3528616978029075170333951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409645274744200454223869 3528616978029075170333951)
                      ·
                        rfl

theorem cell23_6871957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_6871957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871957 prefixEnd_6871957 := by exact prefixLift 6871957
  have htrace : WordTrace (prefixWord ++ tailWord_6871957) baseStart_6871957 baseEnd_6871957 := by
    simpa [prefixWord, tailWord_6871957, baseEnd_6871957] using wordTrace_append hprefix tailTrace_6871957
  have hstable : (prefixWord ++ tailWord_6871957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871957).length < 2 ^ (prefixWord ++ tailWord_6871957).sum := by decide
  have hdescent : baseEnd_6871957 < baseStart_6871957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871958 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6871958 : Nat := 118140960795 + 6871958 * 2 ^ 59
def prefixEnd_6871958 : Nat := 4983230072969 + 3 ^ 40 * 6871958 * 2
def baseEnd_6871958 : Nat := 3528617491509729666421447

theorem tailTrace_6871958 : CollatzResearch.WordTrace tailWord_6871958 prefixEnd_6871958 3528617491509729666421447 := by
  unfold tailWord_6871958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15665056202379829864593533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167093932825384851888997685 15665056202379829864593533)
  ·
    refine ⟨5874396075892436199222575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15665056202379829864593533 5874396075892436199222575)
    ·
      refine ⟨8811594113838654298833863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5874396075892436199222575 8811594113838654298833863)
      ·
        refine ⟨13217391170757981448250795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811594113838654298833863 13217391170757981448250795)
        ·
          refine ⟨19826086756136972172376193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217391170757981448250795 19826086756136972172376193)
          ·
            refine ⟨14869565067102729129282145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19826086756136972172376193 14869565067102729129282145)
            ·
              refine ⟨11152173800327046846961609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14869565067102729129282145 11152173800327046846961609)
              ·
                refine ⟨8364130350245285135221207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11152173800327046846961609 8364130350245285135221207)
                ·
                  refine ⟨12546195525367927702831811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364130350245285135221207 12546195525367927702831811)
                  ·
                    refine ⟨18819293288051891554247717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12546195525367927702831811 18819293288051891554247717)
                    ·
                      refine ⟨3528617491509729666421447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18819293288051891554247717 3528617491509729666421447)
                      ·
                        rfl

theorem cell23_6871958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6871958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871958 prefixEnd_6871958 := by exact prefixLift 6871958
  have htrace : WordTrace (prefixWord ++ tailWord_6871958) baseStart_6871958 baseEnd_6871958 := by
    simpa [prefixWord, tailWord_6871958, baseEnd_6871958] using wordTrace_append hprefix tailTrace_6871958
  have hstable : (prefixWord ++ tailWord_6871958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871958).length < 2 ^ (prefixWord ++ tailWord_6871958).sum := by decide
  have hdescent : baseEnd_6871958 < baseStart_6871958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871964 : List Nat := [2, 2, 3, 3, 2, 2, 2, 7]
def baseStart_6871964 : Nat := 118140960795 + 6871964 * 2 ^ 59
def prefixEnd_6871964 : Nat := 4983230072969 + 3 ^ 40 * 6871964 * 2
def baseEnd_6871964 : Nat := 130689650829394690479497

theorem tailTrace_6871964 : CollatzResearch.WordTrace tailWord_6871964 prefixEnd_6871964 130689650829394690479497 := by
  unfold tailWord_6871964
  simp only [CollatzResearch.WordTrace]
  refine ⟨125320559038027770429107473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167094078717370360572143297 125320559038027770429107473)
  ·
    refine ⟨93990419278520827821830605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125320559038027770429107473 93990419278520827821830605)
    ·
      refine ⟨35246407229445310433186477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93990419278520827821830605 35246407229445310433186477)
      ·
        refine ⟨13217402711041991412444929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35246407229445310433186477 13217402711041991412444929)
        ·
          refine ⟨9913052033281493559333697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13217402711041991412444929 9913052033281493559333697)
          ·
            refine ⟨7434789024961120169500273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913052033281493559333697 7434789024961120169500273)
            ·
              refine ⟨5576091768720840127125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7434789024961120169500273 5576091768720840127125205)
              ·
                refine ⟨130689650829394690479497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5576091768720840127125205 130689650829394690479497)
                ·
                  rfl

theorem cell23_6871964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 7].length) (baseStart_6871964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871964 prefixEnd_6871964 := by exact prefixLift 6871964
  have htrace : WordTrace (prefixWord ++ tailWord_6871964) baseStart_6871964 baseEnd_6871964 := by
    simpa [prefixWord, tailWord_6871964, baseEnd_6871964] using wordTrace_append hprefix tailTrace_6871964
  have hstable : (prefixWord ++ tailWord_6871964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871964).length < 2 ^ (prefixWord ++ tailWord_6871964).sum := by decide
  have hdescent : baseEnd_6871964 < baseStart_6871964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6871975 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6871975 : Nat := 118140960795 + 6871975 * 2 ^ 59
def prefixEnd_6871975 : Nat := 4983230072969 + 3 ^ 40 * 6871975 * 2
def baseEnd_6871975 : Nat := 3528626220680856099908869

theorem tailTrace_6871975 : CollatzResearch.WordTrace tailWord_6871975 prefixEnd_6871975 3528626220680856099908869 := by
  unfold tailWord_6871975
  simp only [CollatzResearch.WordTrace]
  refine ⟨250641519279015689736865379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167094346186010459824576919 250641519279015689736865379)
  ·
    refine ⟨375962278918523534605298069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250641519279015689736865379 375962278918523534605298069)
    ·
      refine ⟨17623231824305790684623347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 375962278918523534605298069 17623231824305790684623347)
      ·
        refine ⟨26434847736458686026935021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17623231824305790684623347 26434847736458686026935021)
        ·
          refine ⟨9913067901172007260100633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26434847736458686026935021 9913067901172007260100633)
          ·
            refine ⟨7434800925879005445075475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913067901172007260100633 7434800925879005445075475)
            ·
              refine ⟨11152201388818508167613213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434800925879005445075475 11152201388818508167613213)
              ·
                refine ⟨4182075520806940562854955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11152201388818508167613213 4182075520806940562854955)
                ·
                  refine ⟨6273113281210410844282433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182075520806940562854955 6273113281210410844282433)
                  ·
                    refine ⟨4704834960907808133211825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6273113281210410844282433 4704834960907808133211825)
                    ·
                      refine ⟨3528626220680856099908869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704834960907808133211825 3528626220680856099908869)
                      ·
                        rfl

theorem cell23_6871975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6871975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6871975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6871975 prefixEnd_6871975 := by exact prefixLift 6871975
  have htrace : WordTrace (prefixWord ++ tailWord_6871975) baseStart_6871975 baseEnd_6871975 := by
    simpa [prefixWord, tailWord_6871975, baseEnd_6871975] using wordTrace_append hprefix tailTrace_6871975
  have hstable : (prefixWord ++ tailWord_6871975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6871975).length < 2 ^ (prefixWord ++ tailWord_6871975).sum := by decide
  have hdescent : baseEnd_6871975 < baseStart_6871975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6871975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872008 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_6872008 : Nat := 118140960795 + 6872008 * 2 ^ 59
def prefixEnd_6872008 : Nat := 4983230072969 + 3 ^ 40 * 6872008 * 2
def baseEnd_6872008 : Nat := 3528643165542454470796217

theorem tailTrace_6872008 : CollatzResearch.WordTrace tailWord_6872008 prefixEnd_6872008 3528643165542454470796217 := by
  unfold tailWord_6872008
  simp only [CollatzResearch.WordTrace]
  refine ⟨125321361443948068186408339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167095148591930757581877785 125321361443948068186408339)
  ·
    refine ⟨187982042165922102279612509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125321361443948068186408339 187982042165922102279612509)
    ·
      refine ⟨70493265812220788354854691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187982042165922102279612509 70493265812220788354854691)
      ·
        refine ⟨105739898718331182532282037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70493265812220788354854691 105739898718331182532282037)
        ·
          refine ⟨9913115504843548362401441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105739898718331182532282037 9913115504843548362401441)
          ·
            refine ⟨7434836628632661271801081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913115504843548362401441 7434836628632661271801081)
            ·
              refine ⟨5576127471474495953850811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7434836628632661271801081 5576127471474495953850811)
              ·
                refine ⟨8364191207211743930776217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576127471474495953850811 8364191207211743930776217)
                ·
                  refine ⟨6273143405408807948082163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364191207211743930776217 6273143405408807948082163)
                  ·
                    refine ⟨9409715108113211922123245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273143405408807948082163 9409715108113211922123245)
                    ·
                      refine ⟨3528643165542454470796217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409715108113211922123245 3528643165542454470796217)
                      ·
                        rfl

theorem cell23_6872008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_6872008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872008 prefixEnd_6872008 := by exact prefixLift 6872008
  have htrace : WordTrace (prefixWord ++ tailWord_6872008) baseStart_6872008 baseEnd_6872008 := by
    simpa [prefixWord, tailWord_6872008, baseEnd_6872008] using wordTrace_append hprefix tailTrace_6872008
  have hstable : (prefixWord ++ tailWord_6872008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872008).length < 2 ^ (prefixWord ++ tailWord_6872008).sum := by decide
  have hdescent : baseEnd_6872008 < baseStart_6872008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872010 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_6872010 : Nat := 118140960795 + 6872010 * 2 ^ 59
def prefixEnd_6872010 : Nat := 4983230072969 + 3 ^ 40 * 6872010 * 2
def baseEnd_6872010 : Nat := 3528644192503763462971207

theorem tailTrace_6872010 : CollatzResearch.WordTrace tailWord_6872010 prefixEnd_6872010 3528644192503763462971207 := by
  unfold tailWord_6872010
  simp only [CollatzResearch.WordTrace]
  refine ⟨62660698958472222678597371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167095197222592593809592989 62660698958472222678597371)
  ·
    refine ⟨93991048437708334017896057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62660698958472222678597371 93991048437708334017896057)
    ·
      refine ⟨70493286328281250513422043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93991048437708334017896057 70493286328281250513422043)
      ·
        refine ⟨105739929492421875770133065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70493286328281250513422043 105739929492421875770133065)
        ·
          refine ⟨79304947119316406827599799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105739929492421875770133065 79304947119316406827599799)
          ·
            refine ⟨118957420678974610241399699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79304947119316406827599799 118957420678974610241399699)
            ·
              refine ⟨178436131018461915362099549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118957420678974610241399699 178436131018461915362099549)
              ·
                refine ⟨66913549131923218260787331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178436131018461915362099549 66913549131923218260787331)
                ·
                  refine ⟨100370323697884827391180997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66913549131923218260787331 100370323697884827391180997)
                  ·
                    refine ⟨18819435693353405135846437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100370323697884827391180997 18819435693353405135846437)
                    ·
                      refine ⟨3528644192503763462971207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18819435693353405135846437 3528644192503763462971207)
                      ·
                        rfl

theorem cell23_6872010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_6872010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872010 prefixEnd_6872010 := by exact prefixLift 6872010
  have htrace : WordTrace (prefixWord ++ tailWord_6872010) baseStart_6872010 baseEnd_6872010 := by
    simpa [prefixWord, tailWord_6872010, baseEnd_6872010] using wordTrace_append hprefix tailTrace_6872010
  have hstable : (prefixWord ++ tailWord_6872010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872010).length < 2 ^ (prefixWord ++ tailWord_6872010).sum := by decide
  have hdescent : baseEnd_6872010 < baseStart_6872010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872018 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6872018 : Nat := 118140960795 + 6872018 * 2 ^ 59
def prefixEnd_6872018 : Nat := 4983230072969 + 3 ^ 40 * 6872018 * 2
def baseEnd_6872018 : Nat := 3528648300348999431671171

theorem tailTrace_6872018 : CollatzResearch.WordTrace tailWord_6872018 prefixEnd_6872018 3528648300348999431671171 := by
  unfold tailWord_6872018
  simp only [CollatzResearch.WordTrace]
  refine ⟨62660771904464977020170177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167095391745239938720453805 62660771904464977020170177)
  ·
    refine ⟨46995578928348732765127633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62660771904464977020170177 46995578928348732765127633)
    ·
      refine ⟨35246684196261549573845725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46995578928348732765127633 35246684196261549573845725)
      ·
        refine ⟨13217506573598081090192147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35246684196261549573845725 13217506573598081090192147)
        ·
          refine ⟨19826259860397121635288221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217506573598081090192147 19826259860397121635288221)
          ·
            refine ⟨7434847447648920613233083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19826259860397121635288221 7434847447648920613233083)
            ·
              refine ⟨11152271171473380919849625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434847447648920613233083 11152271171473380919849625)
              ·
                refine ⟨8364203378605035689887219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11152271171473380919849625 8364203378605035689887219)
                ·
                  refine ⟨12546305067907553534830829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364203378605035689887219 12546305067907553534830829)
                  ·
                    refine ⟨4704864400465332575561561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12546305067907553534830829 4704864400465332575561561)
                    ·
                      refine ⟨3528648300348999431671171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704864400465332575561561 3528648300348999431671171)
                      ·
                        rfl

theorem cell23_6872018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6872018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872018 prefixEnd_6872018 := by exact prefixLift 6872018
  have htrace : WordTrace (prefixWord ++ tailWord_6872018) baseStart_6872018 baseEnd_6872018 := by
    simpa [prefixWord, tailWord_6872018, baseEnd_6872018] using wordTrace_append hprefix tailTrace_6872018
  have hstable : (prefixWord ++ tailWord_6872018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872018).length < 2 ^ (prefixWord ++ tailWord_6872018).sum := by decide
  have hdescent : baseEnd_6872018 < baseStart_6872018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872034 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6872034 : Nat := 118140960795 + 6872034 * 2 ^ 59
def prefixEnd_6872034 : Nat := 4983230072969 + 3 ^ 40 * 6872034 * 2
def baseEnd_6872034 : Nat := 3528656516039471369071097

theorem tailTrace_6872034 : CollatzResearch.WordTrace tailWord_6872034 prefixEnd_6872034 3528656516039471369071097 := by
  unfold tailWord_6872034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62660917796450485703315789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167095780790534628542175437 62660917796450485703315789)
  ·
    refine ⟨23497844173668932138743421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62660917796450485703315789 23497844173668932138743421)
    ·
      refine ⟨8811691565125849552028783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23497844173668932138743421 8811691565125849552028783)
      ·
        refine ⟨13217537347688774328043175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811691565125849552028783 13217537347688774328043175)
        ·
          refine ⟨19826306021533161492064763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217537347688774328043175 19826306021533161492064763)
          ·
            refine ⟨29739459032299742238097145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19826306021533161492064763 29739459032299742238097145)
            ·
              refine ⟨22304594274224806678572859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29739459032299742238097145 22304594274224806678572859)
              ·
                refine ⟨33456891411337210017859289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22304594274224806678572859 33456891411337210017859289)
                ·
                  refine ⟨25092668558502907513394467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33456891411337210017859289 25092668558502907513394467)
                  ·
                    refine ⟨37639002837754361270091701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25092668558502907513394467 37639002837754361270091701)
                    ·
                      refine ⟨3528656516039471369071097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37639002837754361270091701 3528656516039471369071097)
                      ·
                        rfl

theorem cell23_6872034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6872034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872034 prefixEnd_6872034 := by exact prefixLift 6872034
  have htrace : WordTrace (prefixWord ++ tailWord_6872034) baseStart_6872034 baseEnd_6872034 := by
    simpa [prefixWord, tailWord_6872034, baseEnd_6872034] using wordTrace_append hprefix tailTrace_6872034
  have hstable : (prefixWord ++ tailWord_6872034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872034).length < 2 ^ (prefixWord ++ tailWord_6872034).sum := by decide
  have hdescent : baseEnd_6872034 < baseStart_6872034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872057 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 7, 2]
def baseStart_6872057 : Nat := 118140960795 + 6872057 * 2 ^ 59
def prefixEnd_6872057 : Nat := 4983230072969 + 3 ^ 40 * 6872057 * 2
def baseEnd_6872057 : Nat := 3528668326094524779083491

theorem tailTrace_6872057 : CollatzResearch.WordTrace tailWord_6872057 prefixEnd_6872057 3528668326094524779083491 := by
  unfold tailWord_6872057
  simp only [CollatzResearch.WordTrace]
  refine ⟨250644510064718617741350425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167096340043145745160900283 250644510064718617741350425)
  ·
    refine ⟨187983382548538963306012819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250644510064718617741350425 187983382548538963306012819)
    ·
      refine ⟨281975073822808444959019229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187983382548538963306012819 281975073822808444959019229)
      ·
        refine ⟨105740652683553166859632211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281975073822808444959019229 105740652683553166859632211)
        ·
          refine ⟨158610979025329750289448317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105740652683553166859632211 158610979025329750289448317)
          ·
            refine ⟨59479117134498656358543119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158610979025329750289448317 59479117134498656358543119)
            ·
              refine ⟨89218675701747984537814679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59479117134498656358543119 89218675701747984537814679)
              ·
                refine ⟨133828013552621976806722019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89218675701747984537814679 133828013552621976806722019)
                ·
                  refine ⟨200742020328932965210083029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133828013552621976806722019 200742020328932965210083029)
                  ·
                    refine ⟨4704891101459366372111321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 200742020328932965210083029 4704891101459366372111321)
                    ·
                      refine ⟨3528668326094524779083491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4704891101459366372111321 3528668326094524779083491)
                      ·
                        rfl

theorem cell23_6872057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_6872057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872057 prefixEnd_6872057 := by exact prefixLift 6872057
  have htrace : WordTrace (prefixWord ++ tailWord_6872057) baseStart_6872057 baseEnd_6872057 := by
    simpa [prefixWord, tailWord_6872057, baseEnd_6872057] using wordTrace_append hprefix tailTrace_6872057
  have hstable : (prefixWord ++ tailWord_6872057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872057).length < 2 ^ (prefixWord ++ tailWord_6872057).sum := by decide
  have hdescent : baseEnd_6872057 < baseStart_6872057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872107 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3]
def baseStart_6872107 : Nat := 118140960795 + 6872107 * 2 ^ 59
def prefixEnd_6872107 : Nat := 4983230072969 + 3 ^ 40 * 6872107 * 2
def baseEnd_6872107 : Nat := 3528694000127249583458261

theorem tailTrace_6872107 : CollatzResearch.WordTrace tailWord_6872107 prefixEnd_6872107 3528694000127249583458261 := by
  unfold tailWord_6872107
  simp only [CollatzResearch.WordTrace]
  refine ⟨250646333714537476280670575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167097555809691650853780383 250646333714537476280670575)
  ·
    refine ⟨375969500571806214421005863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250646333714537476280670575 375969500571806214421005863)
    ·
      refine ⟨563954250857709321631508795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375969500571806214421005863 563954250857709321631508795)
      ·
        refine ⟨845931376286563982447263193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563954250857709321631508795 845931376286563982447263193)
        ·
          refine ⟨634448532214922986835447395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845931376286563982447263193 634448532214922986835447395)
          ·
            refine ⟨951672798322384480253171093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634448532214922986835447395 951672798322384480253171093)
            ·
              refine ⟨44609662421361772511867395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 951672798322384480253171093 44609662421361772511867395)
              ·
                refine ⟨66914493632042658767801093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44609662421361772511867395 66914493632042658767801093)
                ·
                  refine ⟨12546467556007998518962705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66914493632042658767801093 12546467556007998518962705)
                  ·
                    refine ⟨9409850667005998889222029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12546467556007998518962705 9409850667005998889222029)
                    ·
                      refine ⟨3528694000127249583458261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409850667005998889222029 3528694000127249583458261)
                      ·
                        rfl

theorem cell23_6872107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 3].length) (baseStart_6872107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872107 prefixEnd_6872107 := by exact prefixLift 6872107
  have htrace : WordTrace (prefixWord ++ tailWord_6872107) baseStart_6872107 baseEnd_6872107 := by
    simpa [prefixWord, tailWord_6872107, baseEnd_6872107] using wordTrace_append hprefix tailTrace_6872107
  have hstable : (prefixWord ++ tailWord_6872107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872107).length < 2 ^ (prefixWord ++ tailWord_6872107).sum := by decide
  have hdescent : baseEnd_6872107 < baseStart_6872107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872114 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_6872114 : Nat := 118140960795 + 6872114 * 2 ^ 59
def prefixEnd_6872114 : Nat := 4983230072969 + 3 ^ 40 * 6872114 * 2
def baseEnd_6872114 : Nat := 1176232531497277018690243

theorem tailTrace_6872114 : CollatzResearch.WordTrace tailWord_6872114 prefixEnd_6872114 1176232531497277018690243 := by
  unfold tailWord_6872114
  simp only [CollatzResearch.WordTrace]
  refine ⟨62661647256378029119043849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167097726017008077650783597 62661647256378029119043849)
  ·
    refine ⟨46996235442283521839282887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62661647256378029119043849 46996235442283521839282887)
    ·
      refine ⟨70494353163425282758924331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46996235442283521839282887 70494353163425282758924331)
      ·
        refine ⟨105741529745137924138386497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70494353163425282758924331 105741529745137924138386497)
        ·
          refine ⟨79306147308853443103789873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105741529745137924138386497 79306147308853443103789873)
          ·
            refine ⟨59479610481640082327842405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79306147308853443103789873 59479610481640082327842405)
            ·
              refine ⟨11152426965307515436470451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59479610481640082327842405 11152426965307515436470451)
              ·
                refine ⟨16728640447961273154705677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152426965307515436470451 16728640447961273154705677)
                ·
                  refine ⟨6273240167985477433014629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16728640447961273154705677 6273240167985477433014629)
                  ·
                    refine ⟨1176232531497277018690243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273240167985477433014629 1176232531497277018690243)
                    ·
                      rfl

theorem cell23_6872114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_6872114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872114 prefixEnd_6872114 := by exact prefixLift 6872114
  have htrace : WordTrace (prefixWord ++ tailWord_6872114) baseStart_6872114 baseEnd_6872114 := by
    simpa [prefixWord, tailWord_6872114, baseEnd_6872114] using wordTrace_append hprefix tailTrace_6872114
  have hstable : (prefixWord ++ tailWord_6872114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872114).length < 2 ^ (prefixWord ++ tailWord_6872114).sum := by decide
  have hdescent : baseEnd_6872114 < baseStart_6872114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872158 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6872158 : Nat := 118140960795 + 6872158 * 2 ^ 59
def prefixEnd_6872158 : Nat := 4983230072969 + 3 ^ 40 * 6872158 * 2
def baseEnd_6872158 : Nat := 3528720187640628883920527

theorem tailTrace_6872158 : CollatzResearch.WordTrace tailWord_6872158 prefixEnd_6872158 3528720187640628883920527 := by
  unfold tailWord_6872158
  simp only [CollatzResearch.WordTrace]
  refine ⟨31331024229669088998847141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167098795891568474660518085 31331024229669088998847141)
  ·
    refine ⟨5874567043062954187283839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31331024229669088998847141 5874567043062954187283839)
    ·
      refine ⟨8811850564594431280925759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5874567043062954187283839 8811850564594431280925759)
      ·
        refine ⟨13217775846891646921388639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811850564594431280925759 13217775846891646921388639)
        ·
          refine ⟨19826663770337470382082959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217775846891646921388639 19826663770337470382082959)
          ·
            refine ⟨29739995655506205573124439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19826663770337470382082959 29739995655506205573124439)
            ·
              refine ⟨44609993483259308359686659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29739995655506205573124439 44609993483259308359686659)
              ·
                refine ⟨66914990224888962539529989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44609993483259308359686659 66914990224888962539529989)
                ·
                  refine ⟨12546560667166680476161873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66914990224888962539529989 12546560667166680476161873)
                  ·
                    refine ⟨9409920500375010357121405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12546560667166680476161873 9409920500375010357121405)
                    ·
                      refine ⟨3528720187640628883920527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9409920500375010357121405 3528720187640628883920527)
                      ·
                        rfl

theorem cell23_6872158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6872158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872158 prefixEnd_6872158 := by exact prefixLift 6872158
  have htrace : WordTrace (prefixWord ++ tailWord_6872158) baseStart_6872158 baseEnd_6872158 := by
    simpa [prefixWord, tailWord_6872158, baseEnd_6872158] using wordTrace_append hprefix tailTrace_6872158
  have hstable : (prefixWord ++ tailWord_6872158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872158).length < 2 ^ (prefixWord ++ tailWord_6872158).sum := by decide
  have hdescent : baseEnd_6872158 < baseStart_6872158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872221 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_6872221 : Nat := 118140960795 + 6872221 * 2 ^ 59
def prefixEnd_6872221 : Nat := 4983230072969 + 3 ^ 40 * 6872221 * 2
def baseEnd_6872221 : Nat := 1176250845640620712477579

theorem tailTrace_6872221 : CollatzResearch.WordTrace tailWord_6872221 prefixEnd_6872221 1176250845640620712477579 := by
  unfold tailWord_6872221
  simp only [CollatzResearch.WordTrace]
  refine ⟨250650491636124473750320517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167100327757416315833547011 250650491636124473750320517)
  ·
    refine ⟨46996967181773338828185097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250650491636124473750320517 46996967181773338828185097)
    ·
      refine ⟨35247725386330004121138823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46996967181773338828185097 35247725386330004121138823)
      ·
        refine ⟨52871588079495006181708235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35247725386330004121138823 52871588079495006181708235)
        ·
          refine ⟨79307382119242509272562353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52871588079495006181708235 79307382119242509272562353)
          ·
            refine ⟨59480536589431881954421765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79307382119242509272562353 59480536589431881954421765)
            ·
              refine ⟨11152600610518477866454081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59480536589431881954421765 11152600610518477866454081)
              ·
                refine ⟨8364450457888858399840561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11152600610518477866454081 8364450457888858399840561)
                ·
                  refine ⟨6273337843416643799880421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364450457888858399840561 6273337843416643799880421)
                  ·
                    refine ⟨1176250845640620712477579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273337843416643799880421 1176250845640620712477579)
                    ·
                      rfl

theorem cell23_6872221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_6872221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872221 prefixEnd_6872221 := by exact prefixLift 6872221
  have htrace : WordTrace (prefixWord ++ tailWord_6872221) baseStart_6872221 baseEnd_6872221 := by
    simpa [prefixWord, tailWord_6872221, baseEnd_6872221] using wordTrace_append hprefix tailTrace_6872221
  have hstable : (prefixWord ++ tailWord_6872221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872221).length < 2 ^ (prefixWord ++ tailWord_6872221).sum := by decide
  have hdescent : baseEnd_6872221 < baseStart_6872221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872222 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6872222 : Nat := 118140960795 + 6872222 * 2 ^ 59
def prefixEnd_6872222 : Nat := 4983230072969 + 3 ^ 40 * 6872222 * 2
def baseEnd_6872222 : Nat := 3528753050402516633520233

theorem tailTrace_6872222 : CollatzResearch.WordTrace tailWord_6872222 prefixEnd_6872222 3528753050402516633520233 := by
  unfold tailWord_6872222
  simp only [CollatzResearch.WordTrace]
  refine ⟨31331316013640106365138365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167100352072747233947404613 31331316013640106365138365)
  ·
    refine ⟨11749243505115039886926887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31331316013640106365138365 11749243505115039886926887)
    ·
      refine ⟨17623865257672559830390331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11749243505115039886926887 17623865257672559830390331)
      ·
        refine ⟨26435797886508839745585497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17623865257672559830390331 26435797886508839745585497)
        ·
          refine ⟨19826848414881629809189123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26435797886508839745585497 19826848414881629809189123)
          ·
            refine ⟨29740272622322444713783685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19826848414881629809189123 29740272622322444713783685)
            ·
              refine ⟨5576301116685458383834441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29740272622322444713783685 5576301116685458383834441)
              ·
                refine ⟨4182225837514093787875831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5576301116685458383834441 4182225837514093787875831)
                ·
                  refine ⟨6273338756271140681813747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182225837514093787875831 6273338756271140681813747)
                  ·
                    refine ⟨9410008134406711022720621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273338756271140681813747 9410008134406711022720621)
                    ·
                      refine ⟨3528753050402516633520233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410008134406711022720621 3528753050402516633520233)
                      ·
                        rfl

theorem cell23_6872222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6872222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872222 prefixEnd_6872222 := by exact prefixLift 6872222
  have htrace : WordTrace (prefixWord ++ tailWord_6872222) baseStart_6872222 baseEnd_6872222 := by
    simpa [prefixWord, tailWord_6872222, baseEnd_6872222] using wordTrace_append hprefix tailTrace_6872222
  have hstable : (prefixWord ++ tailWord_6872222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872222).length < 2 ^ (prefixWord ++ tailWord_6872222).sum := by decide
  have hdescent : baseEnd_6872222 < baseStart_6872222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872231 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6872231 : Nat := 118140960795 + 6872231 * 2 ^ 59
def prefixEnd_6872231 : Nat := 4983230072969 + 3 ^ 40 * 6872231 * 2
def baseEnd_6872231 : Nat := 3528757671728407098307691

theorem tailTrace_6872231 : CollatzResearch.WordTrace tailWord_6872231 prefixEnd_6872231 3528757671728407098307691 := by
  unfold tailWord_6872231
  simp only [CollatzResearch.WordTrace]
  refine ⟨250650856366088245458184547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167100570910725496972123031 250650856366088245458184547)
  ·
    refine ⟨375976284549132368187276821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250650856366088245458184547 375976284549132368187276821)
    ·
      refine ⟨17623888338240579758778601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 375976284549132368187276821 17623888338240579758778601)
      ·
        refine ⟨13217916253680434819083951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17623888338240579758778601 13217916253680434819083951)
        ·
          refine ⟨19826874380520652228625927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217916253680434819083951 19826874380520652228625927)
          ·
            refine ⟨29740311570780978342938891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19826874380520652228625927 29740311570780978342938891)
            ·
              refine ⟨44610467356171467514408337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29740311570780978342938891 44610467356171467514408337)
              ·
                refine ⟨33457850517128600635806253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44610467356171467514408337 33457850517128600635806253)
                ·
                  refine ⟨12546693943923225238427345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33457850517128600635806253 12546693943923225238427345)
                  ·
                    refine ⟨9410020457942418928820509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12546693943923225238427345 9410020457942418928820509)
                    ·
                      refine ⟨3528757671728407098307691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9410020457942418928820509 3528757671728407098307691)
                      ·
                        rfl

theorem cell23_6872231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6872231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872231 prefixEnd_6872231 := by exact prefixLift 6872231
  have htrace : WordTrace (prefixWord ++ tailWord_6872231) baseStart_6872231 baseEnd_6872231 := by
    simpa [prefixWord, tailWord_6872231, baseEnd_6872231] using wordTrace_append hprefix tailTrace_6872231
  have hstable : (prefixWord ++ tailWord_6872231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872231).length < 2 ^ (prefixWord ++ tailWord_6872231).sum := by decide
  have hdescent : baseEnd_6872231 < baseStart_6872231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872241 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6872241 : Nat := 118140960795 + 6872241 * 2 ^ 59
def prefixEnd_6872241 : Nat := 4983230072969 + 3 ^ 40 * 6872241 * 2
def baseEnd_6872241 : Nat := 3528762806534952059182645

theorem tailTrace_6872241 : CollatzResearch.WordTrace tailWord_6872241 prefixEnd_6872241 3528762806534952059182645 := by
  unfold tailWord_6872241
  simp only [CollatzResearch.WordTrace]
  refine ⟨250651221096052017166048577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167100814064034678110699051 250651221096052017166048577)
  ·
    refine ⟨187988415822039012874536433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250651221096052017166048577 187988415822039012874536433)
    ·
      refine ⟨140991311866529259655902325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187988415822039012874536433 140991311866529259655902325)
      ·
        refine ⟨13217935487487118092740843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140991311866529259655902325 13217935487487118092740843)
        ·
          refine ⟨19826903231230677139111265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217935487487118092740843 19826903231230677139111265)
          ·
            refine ⟨14870177423423007854333449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19826903231230677139111265 14870177423423007854333449)
            ·
              refine ⟨11152633067567255890750087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14870177423423007854333449 11152633067567255890750087)
              ·
                refine ⟨16728949601350883836125131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152633067567255890750087 16728949601350883836125131)
                ·
                  refine ⟨25093424402026325754187697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16728949601350883836125131 25093424402026325754187697)
                  ·
                    refine ⟨18820068301519744315640773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25093424402026325754187697 18820068301519744315640773)
                    ·
                      refine ⟨3528762806534952059182645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18820068301519744315640773 3528762806534952059182645)
                      ·
                        rfl

theorem cell23_6872241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6872241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872241 prefixEnd_6872241 := by exact prefixLift 6872241
  have htrace : WordTrace (prefixWord ++ tailWord_6872241) baseStart_6872241 baseEnd_6872241 := by
    simpa [prefixWord, tailWord_6872241, baseEnd_6872241] using wordTrace_append hprefix tailTrace_6872241
  have hstable : (prefixWord ++ tailWord_6872241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872241).length < 2 ^ (prefixWord ++ tailWord_6872241).sum := by decide
  have hdescent : baseEnd_6872241 < baseStart_6872241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872247 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 7]
def baseStart_6872247 : Nat := 118140960795 + 6872247 * 2 ^ 59
def prefixEnd_6872247 : Nat := 4983230072969 + 3 ^ 40 * 6872247 * 2
def baseEnd_6872247 : Nat := 1176255295806293011902539

theorem tailTrace_6872247 : CollatzResearch.WordTrace tailWord_6872247 prefixEnd_6872247 1176255295806293011902539 := by
  unfold tailWord_6872247
  simp only [CollatzResearch.WordTrace]
  refine ⟨250651439934030280190766995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167100959956020186793844663 250651439934030280190766995)
  ·
    refine ⟨375977159901045420286150493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250651439934030280190766995 375977159901045420286150493)
    ·
      refine ⟨140991434962892032607306435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375977159901045420286150493 140991434962892032607306435)
      ·
        refine ⟨211487152444338048910959653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140991434962892032607306435 211487152444338048910959653)
        ·
          refine ⟨39653841083313384170804935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211487152444338048910959653 39653841083313384170804935)
          ·
            refine ⟨59480761624970076256207403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39653841083313384170804935 59480761624970076256207403)
            ·
              refine ⟨89221142437455114384311105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59480761624970076256207403 89221142437455114384311105)
              ·
                refine ⟨66915856828091335788233329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89221142437455114384311105 66915856828091335788233329)
                ·
                  refine ⟨50186892621068501841174997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66915856828091335788233329 50186892621068501841174997)
                  ·
                    refine ⟨1176255295806293011902539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50186892621068501841174997 1176255295806293011902539)
                    ·
                      rfl

theorem cell23_6872247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_6872247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872247 prefixEnd_6872247 := by exact prefixLift 6872247
  have htrace : WordTrace (prefixWord ++ tailWord_6872247) baseStart_6872247 baseEnd_6872247 := by
    simpa [prefixWord, tailWord_6872247, baseEnd_6872247] using wordTrace_append hprefix tailTrace_6872247
  have hstable : (prefixWord ++ tailWord_6872247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872247).length < 2 ^ (prefixWord ++ tailWord_6872247).sum := by decide
  have hdescent : baseEnd_6872247 < baseStart_6872247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6872262 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6872262 : Nat := 118140960795 + 6872262 * 2 ^ 59
def prefixEnd_6872262 : Nat := 4983230072969 + 3 ^ 40 * 6872262 * 2
def baseEnd_6872262 : Nat := 3528773589628696477020049

theorem tailTrace_6872262 : CollatzResearch.WordTrace tailWord_6872262 prefixEnd_6872262 3528773589628696477020049 := by
  unfold tailWord_6872262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832874594655498054767595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167101324685983958501708693 7832874594655498054767595)
  ·
    refine ⟨11749311891983247082151393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7832874594655498054767595 11749311891983247082151393)
    ·
      refine ⟨8811983918987435311613545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11749311891983247082151393 8811983918987435311613545)
      ·
        refine ⟨6608987939240576483710159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8811983918987435311613545 6608987939240576483710159)
        ·
          refine ⟨9913481908860864725565239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608987939240576483710159 9913481908860864725565239)
          ·
            refine ⟨14870222863291297088347859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9913481908860864725565239 14870222863291297088347859)
            ·
              refine ⟨22305334294936945632521789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14870222863291297088347859 22305334294936945632521789)
              ·
                refine ⟨8364500360601354612195671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22305334294936945632521789 8364500360601354612195671)
                ·
                  refine ⟨12546750540902031918293507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364500360601354612195671 12546750540902031918293507)
                  ·
                    refine ⟨18820125811353047877440261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12546750540902031918293507 18820125811353047877440261)
                    ·
                      refine ⟨3528773589628696477020049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18820125811353047877440261 3528773589628696477020049)
                      ·
                        rfl

theorem cell23_6872262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6872262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6872262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6872262 prefixEnd_6872262 := by exact prefixLift 6872262
  have htrace : WordTrace (prefixWord ++ tailWord_6872262) baseStart_6872262 baseEnd_6872262 := by
    simpa [prefixWord, tailWord_6872262, baseEnd_6872262] using wordTrace_append hprefix tailTrace_6872262
  have hstable : (prefixWord ++ tailWord_6872262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6872262).length < 2 ^ (prefixWord ++ tailWord_6872262).sum := by decide
  have hdescent : baseEnd_6872262 < baseStart_6872262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6872262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
