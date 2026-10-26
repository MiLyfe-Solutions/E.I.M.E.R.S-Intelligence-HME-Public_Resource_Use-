import V185TrunkScan23Chunk0342

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2029107 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 3]
def baseStart_2029107 : Nat := 118140960795 + 2029107 * 2 ^ 59
def prefixEnd_2029107 : Nat := 4983230072969 + 3 ^ 40 * 2029107 * 2
def baseEnd_2029107 : Nat := 1041907190402697843230813

theorem tailTrace_2029107 : CollatzResearch.WordTrace tailWord_2029107 prefixEnd_2029107 1041907190402697843230813 := by
  unfold tailWord_2029107
  simp only [CollatzResearch.WordTrace]
  refine ⟨74007612259899357730941575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49338408173266238487294383 74007612259899357730941575)
  ·
    refine ⟨111011418389849036596412363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74007612259899357730941575 111011418389849036596412363)
    ·
      refine ⟨166517127584773554894618545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111011418389849036596412363 166517127584773554894618545)
      ·
        refine ⟨124887845688580166170963909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166517127584773554894618545 124887845688580166170963909)
        ·
          refine ⟨23416471066608781157055733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124887845688580166170963909 23416471066608781157055733)
          ·
            refine ⟨2195294162494573233473975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23416471066608781157055733 2195294162494573233473975)
            ·
              refine ⟨3292941243741859850210963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195294162494573233473975 3292941243741859850210963)
              ·
                refine ⟨4939411865612789775316445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292941243741859850210963 4939411865612789775316445)
                ·
                  refine ⟨1852279449604796165743667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4939411865612789775316445 1852279449604796165743667)
                  ·
                    refine ⟨2778419174407194248615501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852279449604796165743667 2778419174407194248615501)
                    ·
                      refine ⟨1041907190402697843230813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778419174407194248615501 1041907190402697843230813)
                      ·
                        rfl

theorem cell23_2029107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_2029107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029107 prefixEnd_2029107 := by exact prefixLift 2029107
  have htrace : WordTrace (prefixWord ++ tailWord_2029107) baseStart_2029107 baseEnd_2029107 := by
    simpa [prefixWord, tailWord_2029107, baseEnd_2029107] using wordTrace_append hprefix tailTrace_2029107
  have hstable : (prefixWord ++ tailWord_2029107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029107).length < 2 ^ (prefixWord ++ tailWord_2029107).sum := by decide
  have hdescent : baseEnd_2029107 < baseStart_2029107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029127 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 1, 5]
def baseStart_2029127 : Nat := 118140960795 + 2029127 * 2 ^ 59
def prefixEnd_2029127 : Nat := 4983230072969 + 3 ^ 40 * 2029127 * 2
def baseEnd_2029127 : Nat := 347305820005262588326907

theorem tailTrace_2029127 : CollatzResearch.WordTrace tailWord_2029127 prefixEnd_2029127 347305820005262588326907 := by
  unfold tailWord_2029127
  simp only [CollatzResearch.WordTrace]
  refine ⟨74008341719826901146669635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49338894479884600764446423 74008341719826901146669635)
  ·
    refine ⟨111012512579740351720004453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74008341719826901146669635 111012512579740351720004453)
    ·
      refine ⟨20814846108701315947500835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111012512579740351720004453 20814846108701315947500835)
      ·
        refine ⟨31222269163051973921251253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20814846108701315947500835 31222269163051973921251253)
        ·
          refine ⟨2927087734036122555117305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31222269163051973921251253 2927087734036122555117305)
          ·
            refine ⟨2195315800527091916337979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2927087734036122555117305 2195315800527091916337979)
            ·
              refine ⟨3292973700790637874506969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195315800527091916337979 3292973700790637874506969)
              ·
                refine ⟨2469730275592978405880227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292973700790637874506969 2469730275592978405880227)
                ·
                  refine ⟨3704595413389467608820341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469730275592978405880227 3704595413389467608820341)
                  ·
                    refine ⟨347305820005262588326907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3704595413389467608820341 347305820005262588326907)
                    ·
                      rfl

theorem cell23_2029127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_2029127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029127 prefixEnd_2029127 := by exact prefixLift 2029127
  have htrace : WordTrace (prefixWord ++ tailWord_2029127) baseStart_2029127 baseEnd_2029127 := by
    simpa [prefixWord, tailWord_2029127, baseEnd_2029127] using wordTrace_append hprefix tailTrace_2029127
  have hstable : (prefixWord ++ tailWord_2029127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029127).length < 2 ^ (prefixWord ++ tailWord_2029127).sum := by decide
  have hdescent : baseEnd_2029127 < baseStart_2029127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029136 : List Nat := [2, 1, 1, 1, 1, 3, 3, 11]
def baseStart_2029136 : Nat := 118140960795 + 2029136 * 2 ^ 59
def prefixEnd_2029136 : Nat := 4983230072969 + 3 ^ 40 * 2029136 * 2
def baseEnd_2029136 : Nat := 38589706716358452954377

theorem tailTrace_2029136 : CollatzResearch.WordTrace tailWord_2029136 prefixEnd_2029136 38589706716358452954377 := by
  unfold tailWord_2029136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37004334988397147841873631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49339113317862863789164841 37004334988397147841873631)
  ·
    refine ⟨55506502482595721762810447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37004334988397147841873631 55506502482595721762810447)
    ·
      refine ⟨83259753723893582644215671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55506502482595721762810447 83259753723893582644215671)
      ·
        refine ⟨124889630585840373966323507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83259753723893582644215671 124889630585840373966323507)
        ·
          refine ⟨187334445878760560949485261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124889630585840373966323507 187334445878760560949485261)
          ·
            refine ⟨70250417204535210356056973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187334445878760560949485261 70250417204535210356056973)
            ·
              refine ⟨26343906451700703883521365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70250417204535210356056973 26343906451700703883521365)
              ·
                refine ⟨38589706716358452954377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26343906451700703883521365 38589706716358452954377)
                ·
                  rfl

theorem cell23_2029136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 11].length) (baseStart_2029136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029136 prefixEnd_2029136 := by exact prefixLift 2029136
  have htrace : WordTrace (prefixWord ++ tailWord_2029136) baseStart_2029136 baseEnd_2029136 := by
    simpa [prefixWord, tailWord_2029136, baseEnd_2029136] using wordTrace_append hprefix tailTrace_2029136
  have hstable : (prefixWord ++ tailWord_2029136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029136).length < 2 ^ (prefixWord ++ tailWord_2029136).sum := by decide
  have hdescent : baseEnd_2029136 < baseStart_2029136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029143 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2029143 : Nat := 118140960795 + 2029143 * 2 ^ 59
def prefixEnd_2029143 : Nat := 4983230072969 + 3 ^ 40 * 2029143 * 2
def baseEnd_2029143 : Nat := 1041925675706259702380647

theorem tailTrace_2029143 : CollatzResearch.WordTrace tailWord_2029143 prefixEnd_2029143 1041925675706259702380647 := by
  unfold tailWord_2029143
  simp only [CollatzResearch.WordTrace]
  refine ⟨74008925287768935879252083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49339283525179290586168055 74008925287768935879252083)
  ·
    refine ⟨111013387931653403818878125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74008925287768935879252083 111013387931653403818878125)
    ·
      refine ⟨41630020474370026432079297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111013387931653403818878125 41630020474370026432079297)
      ·
        refine ⟨31222515355777519824059473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41630020474370026432079297 31222515355777519824059473)
        ·
          refine ⟨23416886516833139868044605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31222515355777519824059473 23416886516833139868044605)
          ·
            refine ⟨8781332443812427450516727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23416886516833139868044605 8781332443812427450516727)
            ·
              refine ⟨13171998665718641175775091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781332443812427450516727 13171998665718641175775091)
              ·
                refine ⟨19757997998577961763662637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13171998665718641175775091 19757997998577961763662637)
                ·
                  refine ⟨7409249249466735661373489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19757997998577961763662637 7409249249466735661373489)
                  ·
                    refine ⟨5556936937100051746030117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7409249249466735661373489 5556936937100051746030117)
                    ·
                      refine ⟨1041925675706259702380647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5556936937100051746030117 1041925675706259702380647)
                      ·
                        rfl

theorem cell23_2029143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2029143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029143 prefixEnd_2029143 := by exact prefixLift 2029143
  have htrace : WordTrace (prefixWord ++ tailWord_2029143) baseStart_2029143 baseEnd_2029143 := by
    simpa [prefixWord, tailWord_2029143, baseEnd_2029143] using wordTrace_append hprefix tailTrace_2029143
  have hstable : (prefixWord ++ tailWord_2029143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029143).length < 2 ^ (prefixWord ++ tailWord_2029143).sum := by decide
  have hdescent : baseEnd_2029143 < baseStart_2029143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029157 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_2029157 : Nat := 118140960795 + 2029157 * 2 ^ 59
def prefixEnd_2029157 : Nat := 4983230072969 + 3 ^ 40 * 2029157 * 2
def baseEnd_2029157 : Nat := 347310954811807549201861

theorem tailTrace_2029157 : CollatzResearch.WordTrace tailWord_2029157 prefixEnd_2029157 347310954811807549201861 := by
  unfold tailWord_2029157
  simp only [CollatzResearch.WordTrace]
  refine ⟨74009435909718216270261725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49339623939812144180174483 74009435909718216270261725)
  ·
    refine ⟨27753538466144331101348147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74009435909718216270261725 27753538466144331101348147)
    ·
      refine ⟨41630307699216496652022221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27753538466144331101348147 41630307699216496652022221)
      ·
        refine ⟨15611365387206186244508333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41630307699216496652022221 15611365387206186244508333)
        ·
          refine ⟨5854262020202319841690625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15611365387206186244508333 5854262020202319841690625)
          ·
            refine ⟨4390696515151739881267969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5854262020202319841690625 4390696515151739881267969)
            ·
              refine ⟨3293022386363804910950977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390696515151739881267969 3293022386363804910950977)
              ·
                refine ⟨2469766789772853683213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293022386363804910950977 2469766789772853683213233)
                ·
                  refine ⟨1852325092329640262409925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469766789772853683213233 1852325092329640262409925)
                  ·
                    refine ⟨347310954811807549201861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852325092329640262409925 347310954811807549201861)
                    ·
                      rfl

theorem cell23_2029157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_2029157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029157 prefixEnd_2029157 := by exact prefixLift 2029157
  have htrace : WordTrace (prefixWord ++ tailWord_2029157) baseStart_2029157 baseEnd_2029157 := by
    simpa [prefixWord, tailWord_2029157, baseEnd_2029157] using wordTrace_append hprefix tailTrace_2029157
  have hstable : (prefixWord ++ tailWord_2029157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029157).length < 2 ^ (prefixWord ++ tailWord_2029157).sum := by decide
  have hdescent : baseEnd_2029157 < baseStart_2029157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029170 : List Nat := [3, 2, 1, 2, 3, 3, 1, 8]
def baseStart_2029170 : Nat := 118140960795 + 2029170 * 2 ^ 59
def prefixEnd_2029170 : Nat := 4983230072969 + 3 ^ 40 * 2029170 * 2
def baseEnd_2029170 : Nat := 38590353321627077657149

theorem tailTrace_2029170 : CollatzResearch.WordTrace tailWord_2029170 prefixEnd_2029170 38590353321627077657149 := by
  unfold tailWord_2029170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502477514667779872621241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49339940039114079660323309 18502477514667779872621241)
  ·
    refine ⟨13876858136000834904465931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18502477514667779872621241 13876858136000834904465931)
    ·
      refine ⟨20815287204001252356698897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876858136000834904465931 20815287204001252356698897)
      ·
        refine ⟨15611465403000939267524173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20815287204001252356698897 15611465403000939267524173)
        ·
          refine ⟨5854299526125352225321565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15611465403000939267524173 5854299526125352225321565)
          ·
            refine ⟨2195362322297007084495587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5854299526125352225321565 2195362322297007084495587)
            ·
              refine ⟨3293043483445510626743381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195362322297007084495587 3293043483445510626743381)
              ·
                refine ⟨38590353321627077657149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3293043483445510626743381 38590353321627077657149)
                ·
                  rfl

theorem cell23_2029170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_2029170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029170 prefixEnd_2029170 := by exact prefixLift 2029170
  have htrace : WordTrace (prefixWord ++ tailWord_2029170) baseStart_2029170 baseEnd_2029170 := by
    simpa [prefixWord, tailWord_2029170, baseEnd_2029170] using wordTrace_append hprefix tailTrace_2029170
  have hstable : (prefixWord ++ tailWord_2029170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029170).length < 2 ^ (prefixWord ++ tailWord_2029170).sum := by decide
  have hdescent : baseEnd_2029170 < baseStart_2029170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029180 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_2029180 : Nat := 118140960795 + 2029180 * 2 ^ 59
def prefixEnd_2029180 : Nat := 4983230072969 + 3 ^ 40 * 2029180 * 2
def baseEnd_2029180 : Nat := 1041944674490476057617977

theorem tailTrace_2029180 : CollatzResearch.WordTrace tailWord_2029180 prefixEnd_2029180 1041944674490476057617977 := by
  unfold tailWord_2029180
  simp only [CollatzResearch.WordTrace]
  refine ⟨37005137394317445599174497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49340183192423260798899329 37005137394317445599174497)
  ·
    refine ⟨27753853045738084199380873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37005137394317445599174497 27753853045738084199380873)
    ·
      refine ⟨20815389784303563149535655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27753853045738084199380873 20815389784303563149535655)
      ·
        refine ⟨31223084676455344724303483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20815389784303563149535655 31223084676455344724303483)
        ·
          refine ⟨46834627014683017086455225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31223084676455344724303483 46834627014683017086455225)
          ·
            refine ⟨35125970261012262814841419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46834627014683017086455225 35125970261012262814841419)
            ·
              refine ⟨52688955391518394222262129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35125970261012262814841419 52688955391518394222262129)
              ·
                refine ⟨39516716543638795666696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52688955391518394222262129 39516716543638795666696597)
                ·
                  refine ⟨1852346087983068546876403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39516716543638795666696597 1852346087983068546876403)
                  ·
                    refine ⟨2778519131974602820314605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852346087983068546876403 2778519131974602820314605)
                    ·
                      refine ⟨1041944674490476057617977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778519131974602820314605 1041944674490476057617977)
                      ·
                        rfl

theorem cell23_2029180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_2029180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029180 prefixEnd_2029180 := by exact prefixLift 2029180
  have htrace : WordTrace (prefixWord ++ tailWord_2029180) baseStart_2029180 baseEnd_2029180 := by
    simpa [prefixWord, tailWord_2029180, baseEnd_2029180] using wordTrace_append hprefix tailTrace_2029180
  have hstable : (prefixWord ++ tailWord_2029180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029180).length < 2 ^ (prefixWord ++ tailWord_2029180).sum := by decide
  have hdescent : baseEnd_2029180 < baseStart_2029180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029214 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2029214 : Nat := 118140960795 + 2029214 * 2 ^ 59
def prefixEnd_2029214 : Nat := 4983230072969 + 3 ^ 40 * 2029214 * 2
def baseEnd_2029214 : Nat := 1041962132832728924592821

theorem tailTrace_2029214 : CollatzResearch.WordTrace tailWord_2029214 prefixEnd_2029214 1041962132832728924592821 := by
  unfold tailWord_2029214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251439358813964375635837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49341009913674476670057797 9251439358813964375635837)
  ·
    refine ⟨3469289759555236640863439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9251439358813964375635837 3469289759555236640863439)
    ·
      refine ⟨5203934639332854961295159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469289759555236640863439 5203934639332854961295159)
      ·
        refine ⟨7805901958999282441942739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5203934639332854961295159 7805901958999282441942739)
        ·
          refine ⟨11708852938498923662914109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805901958999282441942739 11708852938498923662914109)
          ·
            refine ⟨4390819851937096373592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11708852938498923662914109 4390819851937096373592791)
            ·
              refine ⟨6586229777905644560389187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390819851937096373592791 6586229777905644560389187)
              ·
                refine ⟨9879344666858466840583781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586229777905644560389187 9879344666858466840583781)
                ·
                  refine ⟨1852377125035962532609459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9879344666858466840583781 1852377125035962532609459)
                  ·
                    refine ⟨2778565687553943798914189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852377125035962532609459 2778565687553943798914189)
                    ·
                      refine ⟨1041962132832728924592821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778565687553943798914189 1041962132832728924592821)
                      ·
                        rfl

theorem cell23_2029214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2029214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029214 prefixEnd_2029214 := by exact prefixLift 2029214
  have htrace : WordTrace (prefixWord ++ tailWord_2029214) baseStart_2029214 baseEnd_2029214 := by
    simpa [prefixWord, tailWord_2029214, baseEnd_2029214] using wordTrace_append hprefix tailTrace_2029214
  have hstable : (prefixWord ++ tailWord_2029214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029214).length < 2 ^ (prefixWord ++ tailWord_2029214).sum := by decide
  have hdescent : baseEnd_2029214 < baseStart_2029214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029288 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2029288 : Nat := 118140960795 + 2029288 * 2 ^ 59
def prefixEnd_2029288 : Nat := 4983230072969 + 3 ^ 40 * 2029288 * 2
def baseEnd_2029288 : Nat := 1042000130401161635067481

theorem tailTrace_2029288 : CollatzResearch.WordTrace tailWord_2029288 prefixEnd_2029288 1042000130401161635067481 := by
  unfold tailWord_2029288
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007106936121812821640259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49342809248162417095520345 37007106936121812821640259)
  ·
    refine ⟨55510660404182719232460389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37007106936121812821640259 55510660404182719232460389)
    ·
      refine ⟨10408248825784259856086323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55510660404182719232460389 10408248825784259856086323)
      ·
        refine ⟨15612373238676389784129485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408248825784259856086323 15612373238676389784129485)
        ·
          refine ⟨5854639964503646169048557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15612373238676389784129485 5854639964503646169048557)
          ·
            refine ⟨2195489986688867313393209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5854639964503646169048557 2195489986688867313393209)
            ·
              refine ⟨1646617490016650485044907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195489986688867313393209 1646617490016650485044907)
              ·
                refine ⟨2469926235024975727567361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646617490016650485044907 2469926235024975727567361)
                ·
                  refine ⟨1852444676268731795675521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469926235024975727567361 1852444676268731795675521)
                  ·
                    refine ⟨1389333507201548846756641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852444676268731795675521 1389333507201548846756641)
                    ·
                      refine ⟨1042000130401161635067481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389333507201548846756641 1042000130401161635067481)
                      ·
                        rfl

theorem cell23_2029288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2029288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029288 prefixEnd_2029288 := by exact prefixLift 2029288
  have htrace : WordTrace (prefixWord ++ tailWord_2029288) baseStart_2029288 baseEnd_2029288 := by
    simpa [prefixWord, tailWord_2029288, baseEnd_2029288] using wordTrace_append hprefix tailTrace_2029288
  have hstable : (prefixWord ++ tailWord_2029288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029288).length < 2 ^ (prefixWord ++ tailWord_2029288).sum := by decide
  have hdescent : baseEnd_2029288 < baseStart_2029288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029303 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 8]
def baseStart_2029303 : Nat := 118140960795 + 2029303 * 2 ^ 59
def prefixEnd_2029303 : Nat := 4983230072969 + 3 ^ 40 * 2029303 * 2
def baseEnd_2029303 : Nat := 347335944203659692126637

theorem tailTrace_2029303 : CollatzResearch.WordTrace tailWord_2029303 prefixEnd_2029303 347335944203659692126637 := by
  unfold tailWord_2029303
  simp only [CollatzResearch.WordTrace]
  refine ⟨74014760967189283205076563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49343173978126188803384375 74014760967189283205076563)
  ·
    refine ⟨111022141450783924807614845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74014760967189283205076563 111022141450783924807614845)
    ·
      refine ⟨41633303044043971802855567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111022141450783924807614845 41633303044043971802855567)
      ·
        refine ⟨62449954566065957704283351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41633303044043971802855567 62449954566065957704283351)
        ·
          refine ⟨93674931849098936556425027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62449954566065957704283351 93674931849098936556425027)
          ·
            refine ⟨140512397773648404834637541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93674931849098936556425027 140512397773648404834637541)
            ·
              refine ⟨26346074582559075906494539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140512397773648404834637541 26346074582559075906494539)
              ·
                refine ⟨39519111873838613859741809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26346074582559075906494539 39519111873838613859741809)
                ·
                  refine ⟨29639333905378960394806357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39519111873838613859741809 29639333905378960394806357)
                  ·
                    refine ⟨347335944203659692126637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29639333905378960394806357 347335944203659692126637)
                    ·
                      rfl

theorem cell23_2029303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_2029303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029303 prefixEnd_2029303 := by exact prefixLift 2029303
  have htrace : WordTrace (prefixWord ++ tailWord_2029303) baseStart_2029303 baseEnd_2029303 := by
    simpa [prefixWord, tailWord_2029303, baseEnd_2029303] using wordTrace_append hprefix tailTrace_2029303
  have hstable : (prefixWord ++ tailWord_2029303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029303).length < 2 ^ (prefixWord ++ tailWord_2029303).sum := by decide
  have hdescent : baseEnd_2029303 < baseStart_2029303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029364 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2029364 : Nat := 118140960795 + 2029364 * 2 ^ 59
def prefixEnd_2029364 : Nat := 4983230072969 + 3 ^ 40 * 2029364 * 2
def baseEnd_2029364 : Nat := 1042039154930903337717131

theorem tailTrace_2029364 : CollatzResearch.WordTrace tailWord_2029364 prefixEnd_2029364 1042039154930903337717131 := by
  unfold tailWord_2029364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37008492909984145311523573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49344657213312193748698097 37008492909984145311523573)
  ·
    refine ⟨3469546210311013622955335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37008492909984145311523573 3469546210311013622955335)
    ·
      refine ⟨5204319315466520434433003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469546210311013622955335 5204319315466520434433003)
      ·
        refine ⟨7806478973199780651649505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204319315466520434433003 7806478973199780651649505)
        ·
          refine ⟨5854859229899835488737129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7806478973199780651649505 5854859229899835488737129)
          ·
            refine ⟨4391144422424876616552847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5854859229899835488737129 4391144422424876616552847)
            ·
              refine ⟨6586716633637314924829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391144422424876616552847 6586716633637314924829271)
              ·
                refine ⟨9880074950455972387243907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586716633637314924829271 9880074950455972387243907)
                ·
                  refine ⟨14820112425683958580865861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9880074950455972387243907 14820112425683958580865861)
                  ·
                    refine ⟨2778771079815742233912349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14820112425683958580865861 2778771079815742233912349)
                    ·
                      refine ⟨1042039154930903337717131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778771079815742233912349 1042039154930903337717131)
                      ·
                        rfl

theorem cell23_2029364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2029364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029364 prefixEnd_2029364 := by exact prefixLift 2029364
  have htrace : WordTrace (prefixWord ++ tailWord_2029364) baseStart_2029364 baseEnd_2029364 := by
    simpa [prefixWord, tailWord_2029364, baseEnd_2029364] using wordTrace_append hprefix tailTrace_2029364
  have hstable : (prefixWord ++ tailWord_2029364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029364).length < 2 ^ (prefixWord ++ tailWord_2029364).sum := by decide
  have hdescent : baseEnd_2029364 < baseStart_2029364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029394 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2029394 : Nat := 118140960795 + 2029394 * 2 ^ 59
def prefixEnd_2029394 : Nat := 4983230072969 + 3 ^ 40 * 2029394 * 2
def baseEnd_2029394 : Nat := 1042054559350538220341993

theorem tailTrace_2029394 : CollatzResearch.WordTrace tailWord_2029394 prefixEnd_2029394 1042054559350538220341993 := by
  unfold tailWord_2029394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504520002464901436659809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49345386673239737164426157 18504520002464901436659809)
  ·
    refine ⟨13878390001848676077494857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18504520002464901436659809 13878390001848676077494857)
    ·
      refine ⟨10408792501386507058121143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13878390001848676077494857 10408792501386507058121143)
      ·
        refine ⟨15613188752079760587181715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408792501386507058121143 15613188752079760587181715)
        ·
          refine ⟨23419783128119640880772573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15613188752079760587181715 23419783128119640880772573)
          ·
            refine ⟨8782418673044865330289715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23419783128119640880772573 8782418673044865330289715)
            ·
              refine ⟨13173628009567297995434573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8782418673044865330289715 13173628009567297995434573)
              ·
                refine ⟨4940110503587736748287965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13173628009567297995434573 4940110503587736748287965)
                ·
                  refine ⟨1852541438845401280607987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4940110503587736748287965 1852541438845401280607987)
                  ·
                    refine ⟨2778812158268101920911981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852541438845401280607987 2778812158268101920911981)
                    ·
                      refine ⟨1042054559350538220341993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778812158268101920911981 1042054559350538220341993)
                      ·
                        rfl

theorem cell23_2029394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2029394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029394 prefixEnd_2029394 := by exact prefixLift 2029394
  have htrace : WordTrace (prefixWord ++ tailWord_2029394) baseStart_2029394 baseEnd_2029394 := by
    simpa [prefixWord, tailWord_2029394, baseEnd_2029394] using wordTrace_append hprefix tailTrace_2029394
  have hstable : (prefixWord ++ tailWord_2029394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029394).length < 2 ^ (prefixWord ++ tailWord_2029394).sum := by decide
  have hdescent : baseEnd_2029394 < baseStart_2029394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029434 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_2029434 : Nat := 118140960795 + 2029434 * 2 ^ 59
def prefixEnd_2029434 : Nat := 4983230072969 + 3 ^ 40 * 2029434 * 2
def baseEnd_2029434 : Nat := 1042075098576718063841809

theorem tailTrace_2029434 : CollatzResearch.WordTrace tailWord_2029434 prefixEnd_2029434 1042075098576718063841809 := by
  unfold tailWord_2029434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504884732428673144523839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49346359286476461718730237 18504884732428673144523839)
  ·
    refine ⟨27757327098643009716785759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18504884732428673144523839 27757327098643009716785759)
    ·
      refine ⟨41635990647964514575178639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27757327098643009716785759 41635990647964514575178639)
      ·
        refine ⟨62453985971946771862767959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41635990647964514575178639 62453985971946771862767959)
        ·
          refine ⟨93680978957920157794151939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62453985971946771862767959 93680978957920157794151939)
          ·
            refine ⟨140521468436880236691227909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93680978957920157794151939 140521468436880236691227909)
            ·
              refine ⟨26347775331915044379605233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140521468436880236691227909 26347775331915044379605233)
              ·
                refine ⟨19760831498936283284703925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26347775331915044379605233 19760831498936283284703925)
                ·
                  refine ⟨1852577953025276557940993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19760831498936283284703925 1852577953025276557940993)
                  ·
                    refine ⟨1389433464768957418455745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852577953025276557940993 1389433464768957418455745)
                    ·
                      refine ⟨1042075098576718063841809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389433464768957418455745 1042075098576718063841809)
                      ·
                        rfl

theorem cell23_2029434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_2029434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029434 prefixEnd_2029434 := by exact prefixLift 2029434
  have htrace : WordTrace (prefixWord ++ tailWord_2029434) baseStart_2029434 baseEnd_2029434 := by
    simpa [prefixWord, tailWord_2029434, baseEnd_2029434] using wordTrace_append hprefix tailTrace_2029434
  have hstable : (prefixWord ++ tailWord_2029434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029434).length < 2 ^ (prefixWord ++ tailWord_2029434).sum := by decide
  have hdescent : baseEnd_2029434 < baseStart_2029434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029437 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2029437 : Nat := 118140960795 + 2029437 * 2 ^ 59
def prefixEnd_2029437 : Nat := 4983230072969 + 3 ^ 40 * 2029437 * 2
def baseEnd_2029437 : Nat := 1042076639018681552104295

theorem tailTrace_2029437 : CollatzResearch.WordTrace tailWord_2029437 prefixEnd_2029437 1042076639018681552104295 := by
  unfold tailWord_2029437
  simp only [CollatzResearch.WordTrace]
  refine ⟨74019648348703824090454565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49346432232469216060303043 74019648348703824090454565)
  ·
    refine ⟨13878684065381967016960231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74019648348703824090454565 13878684065381967016960231)
    ·
      refine ⟨20818026098072950525440347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13878684065381967016960231 20818026098072950525440347)
      ·
        refine ⟨31227039147109425788160521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20818026098072950525440347 31227039147109425788160521)
        ·
          refine ⟨23420279360332069341120391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31227039147109425788160521 23420279360332069341120391)
          ·
            refine ⟨35130419040498104011680587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23420279360332069341120391 35130419040498104011680587)
            ·
              refine ⟨52695628560747156017520881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35130419040498104011680587 52695628560747156017520881)
              ·
                refine ⟨39521721420560367013140661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52695628560747156017520881 39521721420560367013140661)
                ·
                  refine ⟨3705161383177534407481937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39521721420560367013140661 3705161383177534407481937)
                  ·
                    refine ⟨2778871037383150805611453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705161383177534407481937 2778871037383150805611453)
                    ·
                      refine ⟨1042076639018681552104295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778871037383150805611453 1042076639018681552104295)
                      ·
                        rfl

theorem cell23_2029437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2029437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029437 prefixEnd_2029437 := by exact prefixLift 2029437
  have htrace : WordTrace (prefixWord ++ tailWord_2029437) baseStart_2029437 baseEnd_2029437 := by
    simpa [prefixWord, tailWord_2029437, baseEnd_2029437] using wordTrace_append hprefix tailTrace_2029437
  have hstable : (prefixWord ++ tailWord_2029437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029437).length < 2 ^ (prefixWord ++ tailWord_2029437).sum := by decide
  have hdescent : baseEnd_2029437 < baseStart_2029437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029438 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2029438 : Nat := 118140960795 + 2029438 * 2 ^ 59
def prefixEnd_2029438 : Nat := 4983230072969 + 3 ^ 40 * 2029438 * 2
def baseEnd_2029438 : Nat := 1042077152499336048191791

theorem tailTrace_2029438 : CollatzResearch.WordTrace tailWord_2029438 prefixEnd_2029438 1042077152499336048191791 := by
  unfold tailWord_2029438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252460602712525157655121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49346456547800134174160645 9252460602712525157655121)
  ·
    refine ⟨6939345452034393868241341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9252460602712525157655121 6939345452034393868241341)
    ·
      refine ⟨2602254544512897700590503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6939345452034393868241341 2602254544512897700590503)
      ·
        refine ⟨3903381816769346550885755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602254544512897700590503 3903381816769346550885755)
        ·
          refine ⟨5855072725154019826328633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903381816769346550885755 5855072725154019826328633)
          ·
            refine ⟨4391304543865514869746475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5855072725154019826328633 4391304543865514869746475)
            ·
              refine ⟨6586956815798272304619713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391304543865514869746475 6586956815798272304619713)
              ·
                refine ⟨4940217611848704228464785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586956815798272304619713 4940217611848704228464785)
                ·
                  refine ⟨3705163208886528171348589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940217611848704228464785 3705163208886528171348589)
                  ·
                    refine ⟨1389436203332448064255721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705163208886528171348589 1389436203332448064255721)
                    ·
                      refine ⟨1042077152499336048191791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389436203332448064255721 1042077152499336048191791)
                      ·
                        rfl

theorem cell23_2029438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2029438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029438 prefixEnd_2029438 := by exact prefixLift 2029438
  have htrace : WordTrace (prefixWord ++ tailWord_2029438) baseStart_2029438 baseEnd_2029438 := by
    simpa [prefixWord, tailWord_2029438, baseEnd_2029438] using wordTrace_append hprefix tailTrace_2029438
  have hstable : (prefixWord ++ tailWord_2029438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029438).length < 2 ^ (prefixWord ++ tailWord_2029438).sum := by decide
  have hdescent : baseEnd_2029438 < baseStart_2029438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029501 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2029501 : Nat := 118140960795 + 2029501 * 2 ^ 59
def prefixEnd_2029501 : Nat := 4983230072969 + 3 ^ 40 * 2029501 * 2
def baseEnd_2029501 : Nat := 1042109501780569301704001

theorem tailTrace_2029501 : CollatzResearch.WordTrace tailWord_2029501 prefixEnd_2029501 1042109501780569301704001 := by
  unfold tailWord_2029501
  simp only [CollatzResearch.WordTrace]
  refine ⟨74021982620471963020784357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49347988413647975347189571 74021982620471963020784357)
  ·
    refine ⟨13879121741338493066397067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74021982620471963020784357 13879121741338493066397067)
    ·
      refine ⟨20818682612007739599595601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13879121741338493066397067 20818682612007739599595601)
      ·
        refine ⟨15614011959005804699696701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20818682612007739599595601 15614011959005804699696701)
        ·
          refine ⟨5855254484627176762386263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15614011959005804699696701 5855254484627176762386263)
          ·
            refine ⟨8782881726940765143579395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855254484627176762386263 8782881726940765143579395)
            ·
              refine ⟨13174322590411147715369093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8782881726940765143579395 13174322590411147715369093)
              ·
                refine ⟨2470185485702090196631705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13174322590411147715369093 2470185485702090196631705)
                ·
                  refine ⟨1852639114276567647473779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470185485702090196631705 1852639114276567647473779)
                  ·
                    refine ⟨2778958671414851471210669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852639114276567647473779 2778958671414851471210669)
                    ·
                      refine ⟨1042109501780569301704001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778958671414851471210669 1042109501780569301704001)
                      ·
                        rfl

theorem cell23_2029501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2029501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029501 prefixEnd_2029501 := by exact prefixLift 2029501
  have htrace : WordTrace (prefixWord ++ tailWord_2029501) baseStart_2029501 baseEnd_2029501 := by
    simpa [prefixWord, tailWord_2029501, baseEnd_2029501] using wordTrace_append hprefix tailTrace_2029501
  have hstable : (prefixWord ++ tailWord_2029501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029501).length < 2 ^ (prefixWord ++ tailWord_2029501).sum := by decide
  have hdescent : baseEnd_2029501 < baseStart_2029501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029502 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_2029502 : Nat := 118140960795 + 2029502 * 2 ^ 59
def prefixEnd_2029502 : Nat := 4983230072969 + 3 ^ 40 * 2029502 * 2
def baseEnd_2029502 : Nat := 1042110015261223797791497

theorem tailTrace_2029502 : CollatzResearch.WordTrace tailWord_2029502 prefixEnd_2029502 1042110015261223797791497 := by
  unfold tailWord_2029502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252752386683542523946345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49348012728978893461047173 9252752386683542523946345)
  ·
    refine ⟨6939564290012656892959759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9252752386683542523946345 6939564290012656892959759)
    ·
      refine ⟨10409346435018985339439639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6939564290012656892959759 10409346435018985339439639)
      ·
        refine ⟨15614019652528478009159459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409346435018985339439639 15614019652528478009159459)
        ·
          refine ⟨23421029478792717013739189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15614019652528478009159459 23421029478792717013739189)
          ·
            refine ⟨2195721513636817220038049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23421029478792717013739189 2195721513636817220038049)
            ·
              refine ⟨1646791135227612915028537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195721513636817220038049 1646791135227612915028537)
              ·
                refine ⟨1235093351420709686271403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646791135227612915028537 1235093351420709686271403)
                ·
                  refine ⟨1852640027131064529407105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235093351420709686271403 1852640027131064529407105)
                  ·
                    refine ⟨1389480020348298397055329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852640027131064529407105 1389480020348298397055329)
                    ·
                      refine ⟨1042110015261223797791497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389480020348298397055329 1042110015261223797791497)
                      ·
                        rfl

theorem cell23_2029502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_2029502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029502 prefixEnd_2029502 := by exact prefixLift 2029502
  have htrace : WordTrace (prefixWord ++ tailWord_2029502) baseStart_2029502 baseEnd_2029502 := by
    simpa [prefixWord, tailWord_2029502, baseEnd_2029502] using wordTrace_append hprefix tailTrace_2029502
  have hstable : (prefixWord ++ tailWord_2029502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029502).length < 2 ^ (prefixWord ++ tailWord_2029502).sum := by decide
  have hdescent : baseEnd_2029502 < baseStart_2029502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029527 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_2029527 : Nat := 118140960795 + 2029527 * 2 ^ 59
def prefixEnd_2029527 : Nat := 4983230072969 + 3 ^ 40 * 2029527 * 2
def baseEnd_2029527 : Nat := 1042122852277586199978881

theorem tailTrace_2029527 : CollatzResearch.WordTrace tailWord_2029527 prefixEnd_2029527 1042122852277586199978881 := by
  unfold tailWord_2029527
  simp only [CollatzResearch.WordTrace]
  refine ⟨74022930918377769461230835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49348620612251846307487223 74022930918377769461230835)
  ·
    refine ⟨111034396377566654191846253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74022930918377769461230835 111034396377566654191846253)
    ·
      refine ⟨41637898641587495321942345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111034396377566654191846253 41637898641587495321942345)
      ·
        refine ⟨31228423981190621491456759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41637898641587495321942345 31228423981190621491456759)
        ·
          refine ⟨46842635971785932237185139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31228423981190621491456759 46842635971785932237185139)
          ·
            refine ⟨70263953957678898355777709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46842635971785932237185139 70263953957678898355777709)
            ·
              refine ⟨26348982734129586883416641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70263953957678898355777709 26348982734129586883416641)
              ·
                refine ⟨19761737050597190162562481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26348982734129586883416641 19761737050597190162562481)
                ·
                  refine ⟨14821302787947892621921861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19761737050597190162562481 14821302787947892621921861)
                  ·
                    refine ⟨2778994272740229866610349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14821302787947892621921861 2778994272740229866610349)
                    ·
                      refine ⟨1042122852277586199978881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778994272740229866610349 1042122852277586199978881)
                      ·
                        rfl

theorem cell23_2029527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_2029527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029527 prefixEnd_2029527 := by exact prefixLift 2029527
  have htrace : WordTrace (prefixWord ++ tailWord_2029527) baseStart_2029527 baseEnd_2029527 := by
    simpa [prefixWord, tailWord_2029527, baseEnd_2029527] using wordTrace_append hprefix tailTrace_2029527
  have hstable : (prefixWord ++ tailWord_2029527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029527).length < 2 ^ (prefixWord ++ tailWord_2029527).sum := by decide
  have hdescent : baseEnd_2029527 < baseStart_2029527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029564 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 5]
def baseStart_2029564 : Nat := 118140960795 + 2029564 * 2 ^ 59
def prefixEnd_2029564 : Nat := 4983230072969 + 3 ^ 40 * 2029564 * 2
def baseEnd_2029564 : Nat := 115793539006866950579579

theorem tailTrace_2029564 : CollatzResearch.WordTrace tailWord_2029564 prefixEnd_2029564 115793539006866950579579 := by
  unfold tailWord_2029564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012140209621862390163873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49349520279495816520218497 37012140209621862390163873)
  ·
    refine ⟨27759105157216396792622905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37012140209621862390163873 27759105157216396792622905)
    ·
      refine ⟨20819328867912297594467179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27759105157216396792622905 20819328867912297594467179)
      ·
        refine ⟨31228993301868446391700769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20819328867912297594467179 31228993301868446391700769)
        ·
          refine ⟨23421744976401334793775577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31228993301868446391700769 23421744976401334793775577)
          ·
            refine ⟨17566308732301001095331683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23421744976401334793775577 17566308732301001095331683)
            ·
              refine ⟨26349463098451501642997525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566308732301001095331683 26349463098451501642997525)
              ·
                refine ⟨1235131082739914139515509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26349463098451501642997525 1235131082739914139515509)
                ·
                  refine ⟨115793539006866950579579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235131082739914139515509 115793539006866950579579)
                  ·
                    rfl

theorem cell23_2029564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_2029564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029564 prefixEnd_2029564 := by exact prefixLift 2029564
  have htrace : WordTrace (prefixWord ++ tailWord_2029564) baseStart_2029564 baseEnd_2029564 := by
    simpa [prefixWord, tailWord_2029564, baseEnd_2029564] using wordTrace_append hprefix tailTrace_2029564
  have hstable : (prefixWord ++ tailWord_2029564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029564).length < 2 ^ (prefixWord ++ tailWord_2029564).sum := by decide
  have hdescent : baseEnd_2029564 < baseStart_2029564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029575 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_2029575 : Nat := 118140960795 + 2029575 * 2 ^ 59
def prefixEnd_2029575 : Nat := 4983230072969 + 3 ^ 40 * 2029575 * 2
def baseEnd_2029575 : Nat := 1042147499349002012178661

theorem tailTrace_2029575 : CollatzResearch.WordTrace tailWord_2029575 prefixEnd_2029575 1042147499349002012178661 := by
  unfold tailWord_2029575
  simp only [CollatzResearch.WordTrace]
  refine ⟨74024681622203873658978179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49349787748135915772652119 74024681622203873658978179)
  ·
    refine ⟨111037022433305810488467269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74024681622203873658978179 111037022433305810488467269)
    ·
      refine ⟨20819441706244839466587613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111037022433305810488467269 20819441706244839466587613)
      ·
        refine ⟨7807290639841814799970355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20819441706244839466587613 7807290639841814799970355)
        ·
          refine ⟨11710935959762722199955533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807290639841814799970355 11710935959762722199955533)
          ·
            refine ⟨4391600984911020824983325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11710935959762722199955533 4391600984911020824983325)
            ·
              refine ⟨1646850369341632809368747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4391600984911020824983325 1646850369341632809368747)
              ·
                refine ⟨2470275554012449214053121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646850369341632809368747 2470275554012449214053121)
                ·
                  refine ⟨1852706665509336910539841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470275554012449214053121 1852706665509336910539841)
                  ·
                    refine ⟨1389529999132002682904881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852706665509336910539841 1389529999132002682904881)
                    ·
                      refine ⟨1042147499349002012178661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389529999132002682904881 1042147499349002012178661)
                      ·
                        rfl

theorem cell23_2029575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_2029575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029575 prefixEnd_2029575 := by exact prefixLift 2029575
  have htrace : WordTrace (prefixWord ++ tailWord_2029575) baseStart_2029575 baseEnd_2029575 := by
    simpa [prefixWord, tailWord_2029575, baseEnd_2029575] using wordTrace_append hprefix tailTrace_2029575
  have hstable : (prefixWord ++ tailWord_2029575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029575).length < 2 ^ (prefixWord ++ tailWord_2029575).sum := by decide
  have hdescent : baseEnd_2029575 < baseStart_2029575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029681 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_2029681 : Nat := 118140960795 + 2029681 * 2 ^ 59
def prefixEnd_2029681 : Nat := 4983230072969 + 3 ^ 40 * 2029681 * 2
def baseEnd_2029681 : Nat := 1042201928298378597453173

theorem tailTrace_2029681 : CollatzResearch.WordTrace tailWord_2029681 prefixEnd_2029681 1042201928298378597453173 := by
  unfold tailWord_2029681
  simp only [CollatzResearch.WordTrace]
  refine ⟨74028547759819853762336897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49352365173213235841557931 74028547759819853762336897)
  ·
    refine ⟨55521410819864890321752673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74028547759819853762336897 55521410819864890321752673)
    ·
      refine ⟨41641058114898667741314505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55521410819864890321752673 41641058114898667741314505)
      ·
        refine ⟨31230793586174000805985879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41641058114898667741314505 31230793586174000805985879)
        ·
          refine ⟨46846190379261001208978819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31230793586174000805985879 46846190379261001208978819)
          ·
            refine ⟨70269285568891501813468229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46846190379261001208978819 70269285568891501813468229)
            ·
              refine ⟨13175491044167156590025293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70269285568891501813468229 13175491044167156590025293)
              ·
                refine ⟨4940809141562683721259485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13175491044167156590025293 4940809141562683721259485)
                ·
                  refine ⟨1852803428086006395472307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4940809141562683721259485 1852803428086006395472307)
                  ·
                    refine ⟨2779205142129009593208461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852803428086006395472307 2779205142129009593208461)
                    ·
                      refine ⟨1042201928298378597453173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779205142129009593208461 1042201928298378597453173)
                      ·
                        rfl

theorem cell23_2029681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_2029681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029681 prefixEnd_2029681 := by exact prefixLift 2029681
  have htrace : WordTrace (prefixWord ++ tailWord_2029681) baseStart_2029681 baseEnd_2029681 := by
    simpa [prefixWord, tailWord_2029681, baseEnd_2029681] using wordTrace_append hprefix tailTrace_2029681
  have hstable : (prefixWord ++ tailWord_2029681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029681).length < 2 ^ (prefixWord ++ tailWord_2029681).sum := by decide
  have hdescent : baseEnd_2029681 < baseStart_2029681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029741 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2029741 : Nat := 118140960795 + 2029741 * 2 ^ 59
def prefixEnd_2029741 : Nat := 4983230072969 + 3 ^ 40 * 2029741 * 2
def baseEnd_2029741 : Nat := 1042232737137648362702897

theorem tailTrace_2029741 : CollatzResearch.WordTrace tailWord_2029741 prefixEnd_2029741 1042232737137648362702897 := by
  unfold tailWord_2029741
  simp only [CollatzResearch.WordTrace]
  refine ⟨74030736139602484009521077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49353824093068322673014051 74030736139602484009521077)
  ·
    refine ⟨6940381513087732875892601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74030736139602484009521077 6940381513087732875892601)
    ·
      refine ⟨5205286134815799656919451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6940381513087732875892601 5205286134815799656919451)
      ·
        refine ⟨7807929202223699485379177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205286134815799656919451 7807929202223699485379177)
        ·
          refine ⟨5855946901667774614034383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7807929202223699485379177 5855946901667774614034383)
          ·
            refine ⟨8783920352501661921051575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855946901667774614034383 8783920352501661921051575)
            ·
              refine ⟨13175880528752492881577363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783920352501661921051575 13175880528752492881577363)
              ·
                refine ⟨19763820793128739322366045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175880528752492881577363 19763820793128739322366045)
                ·
                  refine ⟨7411432797423277245887267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19763820793128739322366045 7411432797423277245887267)
                  ·
                    refine ⟨11117149196134915868830901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411432797423277245887267 11117149196134915868830901)
                    ·
                      refine ⟨1042232737137648362702897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11117149196134915868830901 1042232737137648362702897)
                      ·
                        rfl

theorem cell23_2029741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2029741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029741 prefixEnd_2029741 := by exact prefixLift 2029741
  have htrace : WordTrace (prefixWord ++ tailWord_2029741) baseStart_2029741 baseEnd_2029741 := by
    simpa [prefixWord, tailWord_2029741, baseEnd_2029741] using wordTrace_append hprefix tailTrace_2029741
  have hstable : (prefixWord ++ tailWord_2029741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029741).length < 2 ^ (prefixWord ++ tailWord_2029741).sum := by decide
  have hdescent : baseEnd_2029741 < baseStart_2029741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029751 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_2029751 : Nat := 118140960795 + 2029751 * 2 ^ 59
def prefixEnd_2029751 : Nat := 4983230072969 + 3 ^ 40 * 2029751 * 2
def baseEnd_2029751 : Nat := 1042237871944193323577851

theorem tailTrace_2029751 : CollatzResearch.WordTrace tailWord_2029751 prefixEnd_2029751 1042237871944193323577851 := by
  unfold tailWord_2029751
  simp only [CollatzResearch.WordTrace]
  refine ⟨74031100869566255717385107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49354067246377503811590071 74031100869566255717385107)
  ·
    refine ⟨111046651304349383576077661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74031100869566255717385107 111046651304349383576077661)
    ·
      refine ⟨41642494239131018841029123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111046651304349383576077661 41642494239131018841029123)
      ·
        refine ⟨62463741358696528261543685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41642494239131018841029123 62463741358696528261543685)
        ·
          refine ⟨11711951504755599049039441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62463741358696528261543685 11711951504755599049039441)
          ·
            refine ⟨8783963628566699286779581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711951504755599049039441 8783963628566699286779581)
            ·
              refine ⟨3293986360712512232542343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8783963628566699286779581 3293986360712512232542343)
              ·
                refine ⟨4940979541068768348813515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293986360712512232542343 4940979541068768348813515)
                ·
                  refine ⟨7411469311603152523220273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940979541068768348813515 7411469311603152523220273)
                  ·
                    refine ⟨5558601983702364392415205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7411469311603152523220273 5558601983702364392415205)
                    ·
                      refine ⟨1042237871944193323577851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5558601983702364392415205 1042237871944193323577851)
                      ·
                        rfl

theorem cell23_2029751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_2029751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029751 prefixEnd_2029751 := by exact prefixLift 2029751
  have htrace : WordTrace (prefixWord ++ tailWord_2029751) baseStart_2029751 baseEnd_2029751 := by
    simpa [prefixWord, tailWord_2029751, baseEnd_2029751] using wordTrace_append hprefix tailTrace_2029751
  have hstable : (prefixWord ++ tailWord_2029751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029751).length < 2 ^ (prefixWord ++ tailWord_2029751).sum := by decide
  have hdescent : baseEnd_2029751 < baseStart_2029751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029771 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 3]
def baseStart_2029771 : Nat := 118140960795 + 2029771 * 2 ^ 59
def prefixEnd_2029771 : Nat := 4983230072969 + 3 ^ 40 * 2029771 * 2
def baseEnd_2029771 : Nat := 1042248141557283245327759

theorem tailTrace_2029771 : CollatzResearch.WordTrace tailWord_2029771 prefixEnd_2029771 1042248141557283245327759 := by
  unfold tailWord_2029771
  simp only [CollatzResearch.WordTrace]
  refine ⟨74031830329493799133113167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49354553552995866088742111 74031830329493799133113167)
  ·
    refine ⟨111047745494240698699669751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74031830329493799133113167 111047745494240698699669751)
    ·
      refine ⟨166571618241361048049504627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111047745494240698699669751 166571618241361048049504627)
      ·
        refine ⟨249857427362041572074256941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166571618241361048049504627 249857427362041572074256941)
        ·
          refine ⟨93696535260765589527846353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249857427362041572074256941 93696535260765589527846353)
          ·
            refine ⟨70272401445574192145884765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93696535260765589527846353 70272401445574192145884765)
            ·
              refine ⟨26352150542090322054706787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70272401445574192145884765 26352150542090322054706787)
              ·
                refine ⟨39528225813135483082060181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26352150542090322054706787 39528225813135483082060181)
                ·
                  refine ⟨1852885584990725769471571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39528225813135483082060181 1852885584990725769471571)
                  ·
                    refine ⟨2779328377486088654207357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852885584990725769471571 2779328377486088654207357)
                    ·
                      refine ⟨1042248141557283245327759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779328377486088654207357 1042248141557283245327759)
                      ·
                        rfl

theorem cell23_2029771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 3].length) (baseStart_2029771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029771 prefixEnd_2029771 := by exact prefixLift 2029771
  have htrace : WordTrace (prefixWord ++ tailWord_2029771) baseStart_2029771 baseEnd_2029771 := by
    simpa [prefixWord, tailWord_2029771, baseEnd_2029771] using wordTrace_append hprefix tailTrace_2029771
  have hstable : (prefixWord ++ tailWord_2029771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029771).length < 2 ^ (prefixWord ++ tailWord_2029771).sum := by decide
  have hdescent : baseEnd_2029771 < baseStart_2029771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029804 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_2029804 : Nat := 118140960795 + 2029804 * 2 ^ 59
def prefixEnd_2029804 : Nat := 4983230072969 + 3 ^ 40 * 2029804 * 2
def baseEnd_2029804 : Nat := 347421695472960538738369

theorem tailTrace_2029804 : CollatzResearch.WordTrace tailWord_2029804 prefixEnd_2029804 347421695472960538738369 := by
  unfold tailWord_2029804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016516969187122884532233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49355355958916163846042977 37016516969187122884532233)
  ·
    refine ⟨27762387726890342163399175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37016516969187122884532233 27762387726890342163399175)
    ·
      refine ⟨41643581590335513245098763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27762387726890342163399175 41643581590335513245098763)
      ·
        refine ⟨62465372385503269867648145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41643581590335513245098763 62465372385503269867648145)
        ·
          refine ⟨46849029289127452400736109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62465372385503269867648145 46849029289127452400736109)
          ·
            refine ⟨17568385983422794650276041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46849029289127452400736109 17568385983422794650276041)
            ·
              refine ⟨13176289487567095987707031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17568385983422794650276041 13176289487567095987707031)
              ·
                refine ⟨19764434231350643981560547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13176289487567095987707031 19764434231350643981560547)
                ·
                  refine ⟨29646651347025965972340821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19764434231350643981560547 29646651347025965972340821)
                  ·
                    refine ⟨347421695472960538738369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29646651347025965972340821 347421695472960538738369)
                    ·
                      rfl

theorem cell23_2029804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_2029804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029804 prefixEnd_2029804 := by exact prefixLift 2029804
  have htrace : WordTrace (prefixWord ++ tailWord_2029804) baseStart_2029804 baseEnd_2029804 := by
    simpa [prefixWord, tailWord_2029804, baseEnd_2029804] using wordTrace_append hprefix tailTrace_2029804
  have hstable : (prefixWord ++ tailWord_2029804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029804).length < 2 ^ (prefixWord ++ tailWord_2029804).sum := by decide
  have hdescent : baseEnd_2029804 < baseStart_2029804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029832 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_2029832 : Nat := 118140960795 + 2029832 * 2 ^ 59
def prefixEnd_2029832 : Nat := 4983230072969 + 3 ^ 40 * 2029832 * 2
def baseEnd_2029832 : Nat := 1042279463877207506664979

theorem tailTrace_2029832 : CollatzResearch.WordTrace tailWord_2029832 prefixEnd_2029832 1042279463877207506664979 := by
  unfold tailWord_2029832
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017027591136403275541875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49356036788181871034055833 37017027591136403275541875)
  ·
    refine ⟨55525541386704604913312813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37017027591136403275541875 55525541386704604913312813)
    ·
      refine ⟨20822078020014226842492305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55525541386704604913312813 20822078020014226842492305)
      ·
        refine ⟨15616558515010670131869229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20822078020014226842492305 15616558515010670131869229)
        ·
          refine ⟨5856209443129001299450961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15616558515010670131869229 5856209443129001299450961)
          ·
            refine ⟨4392157082346750974588221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856209443129001299450961 4392157082346750974588221)
            ·
              refine ⟨1647058905880031615470583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4392157082346750974588221 1647058905880031615470583)
              ·
                refine ⟨2470588358820047423205875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647058905880031615470583 2470588358820047423205875)
                ·
                  refine ⟨3705882538230071134808813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470588358820047423205875 3705882538230071134808813)
                  ·
                    refine ⟨1389705951836276675553305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705882538230071134808813 1389705951836276675553305)
                    ·
                      refine ⟨1042279463877207506664979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389705951836276675553305 1042279463877207506664979)
                      ·
                        rfl

theorem cell23_2029832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_2029832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029832 prefixEnd_2029832 := by exact prefixLift 2029832
  have htrace : WordTrace (prefixWord ++ tailWord_2029832) baseStart_2029832 baseEnd_2029832 := by
    simpa [prefixWord, tailWord_2029832, baseEnd_2029832] using wordTrace_append hprefix tailTrace_2029832
  have hstable : (prefixWord ++ tailWord_2029832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029832).length < 2 ^ (prefixWord ++ tailWord_2029832).sum := by decide
  have hdescent : baseEnd_2029832 < baseStart_2029832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029845 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_2029845 : Nat := 118140960795 + 2029845 * 2 ^ 59
def prefixEnd_2029845 : Nat := 4983230072969 + 3 ^ 40 * 2029845 * 2
def baseEnd_2029845 : Nat := 1042286139125715955802419

theorem tailTrace_2029845 : CollatzResearch.WordTrace tailWord_2029845 prefixEnd_2029845 1042286139125715955802419 := by
  unfold tailWord_2029845
  simp only [CollatzResearch.WordTrace]
  refine ⟨74034529331225709771306989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49356352887483806514204659 74034529331225709771306989)
  ·
    refine ⟨27762948499209641164240121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74034529331225709771306989 27762948499209641164240121)
    ·
      refine ⟨20822211374407230873180091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27762948499209641164240121 20822211374407230873180091)
      ·
        refine ⟨31233317061610846309770137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20822211374407230873180091 31233317061610846309770137)
        ·
          refine ⟨23424987796208134732327603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31233317061610846309770137 23424987796208134732327603)
          ·
            refine ⟨35137481694312202098491405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23424987796208134732327603 35137481694312202098491405)
            ·
              refine ⟨13176555635367075786934277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35137481694312202098491405 13176555635367075786934277)
              ·
                refine ⟨2470604181631326710050177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13176555635367075786934277 2470604181631326710050177)
                ·
                  refine ⟨1852953136223495032537633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470604181631326710050177 1852953136223495032537633)
                  ·
                    refine ⟨1389714852167621274403225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1852953136223495032537633 1389714852167621274403225)
                    ·
                      refine ⟨1042286139125715955802419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389714852167621274403225 1042286139125715955802419)
                      ·
                        rfl

theorem cell23_2029845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_2029845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029845 prefixEnd_2029845 := by exact prefixLift 2029845
  have htrace : WordTrace (prefixWord ++ tailWord_2029845) baseStart_2029845 baseEnd_2029845 := by
    simpa [prefixWord, tailWord_2029845, baseEnd_2029845] using wordTrace_append hprefix tailTrace_2029845
  have hstable : (prefixWord ++ tailWord_2029845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029845).length < 2 ^ (prefixWord ++ tailWord_2029845).sum := by decide
  have hdescent : baseEnd_2029845 < baseStart_2029845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029858 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2029858 : Nat := 118140960795 + 2029858 * 2 ^ 59
def prefixEnd_2029858 : Nat := 4983230072969 + 3 ^ 40 * 2029858 * 2
def baseEnd_2029858 : Nat := 1042292814374224404939859

theorem tailTrace_2029858 : CollatzResearch.WordTrace tailWord_2029858 prefixEnd_2029858 1042292814374224404939859 := by
  unfold tailWord_2029858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508750870044653247882557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49356668986785741994353485 18508750870044653247882557)
  ·
    refine ⟨6940781576266744967955959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18508750870044653247882557 6940781576266744967955959)
    ·
      refine ⟨10411172364400117451933939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940781576266744967955959 10411172364400117451933939)
      ·
        refine ⟨15616758546600176177900909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411172364400117451933939 15616758546600176177900909)
        ·
          refine ⟨5856284454975066066712841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15616758546600176177900909 5856284454975066066712841)
          ·
            refine ⟨4392213341231299550034631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856284454975066066712841 4392213341231299550034631)
            ·
              refine ⟨6588320011846949325051947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392213341231299550034631 6588320011846949325051947)
              ·
                refine ⟨9882480017770423987577921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588320011846949325051947 9882480017770423987577921)
                ·
                  refine ⟨7411860013327817990683441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9882480017770423987577921 7411860013327817990683441)
                  ·
                    refine ⟨5558895009995863493012581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7411860013327817990683441 5558895009995863493012581)
                    ·
                      refine ⟨1042292814374224404939859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5558895009995863493012581 1042292814374224404939859)
                      ·
                        rfl

theorem cell23_2029858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2029858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029858 prefixEnd_2029858 := by exact prefixLift 2029858
  have htrace : WordTrace (prefixWord ++ tailWord_2029858) baseStart_2029858 baseEnd_2029858 := by
    simpa [prefixWord, tailWord_2029858, baseEnd_2029858] using wordTrace_append hprefix tailTrace_2029858
  have hstable : (prefixWord ++ tailWord_2029858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029858).length < 2 ^ (prefixWord ++ tailWord_2029858).sum := by decide
  have hdescent : baseEnd_2029858 < baseStart_2029858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029938 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2029938 : Nat := 118140960795 + 2029938 * 2 ^ 59
def prefixEnd_2029938 : Nat := 4983230072969 + 3 ^ 40 * 2029938 * 2
def baseEnd_2029938 : Nat := 1042333892826584091939491

theorem tailTrace_2029938 : CollatzResearch.WordTrace tailWord_2029938 prefixEnd_2029938 1042333892826584091939491 := by
  unfold tailWord_2029938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18509480329972196663610617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49358614213259191102961645 18509480329972196663610617)
  ·
    refine ⟨13882110247479147497707963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18509480329972196663610617 13882110247479147497707963)
    ·
      refine ⟨20823165371218721246561945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13882110247479147497707963 20823165371218721246561945)
      ·
        refine ⟨15617374028414040934921459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20823165371218721246561945 15617374028414040934921459)
        ·
          refine ⟨23426061042621061402382189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617374028414040934921459 23426061042621061402382189)
          ·
            refine ⟨8784772890982898025893321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23426061042621061402382189 8784772890982898025893321)
            ·
              refine ⟨6588579668237173519419991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784772890982898025893321 6588579668237173519419991)
              ·
                refine ⟨9882869502355760279129987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588579668237173519419991 9882869502355760279129987)
                ·
                  refine ⟨14824304253533640418694981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882869502355760279129987 14824304253533640418694981)
                  ·
                    refine ⟨2779557047537557578505309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14824304253533640418694981 2779557047537557578505309)
                    ·
                      refine ⟨1042333892826584091939491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779557047537557578505309 1042333892826584091939491)
                      ·
                        rfl

theorem cell23_2029938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2029938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029938 prefixEnd_2029938 := by exact prefixLift 2029938
  have htrace : WordTrace (prefixWord ++ tailWord_2029938) baseStart_2029938 baseEnd_2029938 := by
    simpa [prefixWord, tailWord_2029938, baseEnd_2029938] using wordTrace_append hprefix tailTrace_2029938
  have hstable : (prefixWord ++ tailWord_2029938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029938).length < 2 ^ (prefixWord ++ tailWord_2029938).sum := by decide
  have hdescent : baseEnd_2029938 < baseStart_2029938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029951 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_2029951 : Nat := 118140960795 + 2029951 * 2 ^ 59
def prefixEnd_2029951 : Nat := 4983230072969 + 3 ^ 40 * 2029951 * 2
def baseEnd_2029951 : Nat := 1042340568075092541076931

theorem tailTrace_2029951 : CollatzResearch.WordTrace tailWord_2029951 prefixEnd_2029951 1042340568075092541076931 := by
  unfold tailWord_2029951
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038395468841689874665707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49358930312561126583110471 74038395468841689874665707)
  ·
    refine ⟨111057593203262534811998561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74038395468841689874665707 111057593203262534811998561)
    ·
      refine ⟨83293194902446901108998921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111057593203262534811998561 83293194902446901108998921)
      ·
        refine ⟨62469896176835175831749191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83293194902446901108998921 62469896176835175831749191)
        ·
          refine ⟨93704844265252763747623787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62469896176835175831749191 93704844265252763747623787)
          ·
            refine ⟨140557266397879145621435681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93704844265252763747623787 140557266397879145621435681)
            ·
              refine ⟨105417949798409359216076761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140557266397879145621435681 105417949798409359216076761)
              ·
                refine ⟨79063462348807019412057571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105417949798409359216076761 79063462348807019412057571)
                ·
                  refine ⟨118595193523210529118086357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79063462348807019412057571 118595193523210529118086357)
                  ·
                    refine ⟨2779574848200246776205149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118595193523210529118086357 2779574848200246776205149)
                    ·
                      refine ⟨1042340568075092541076931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779574848200246776205149 1042340568075092541076931)
                      ·
                        rfl

theorem cell23_2029951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_2029951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029951 prefixEnd_2029951 := by exact prefixLift 2029951
  have htrace : WordTrace (prefixWord ++ tailWord_2029951) baseStart_2029951 baseEnd_2029951 := by
    simpa [prefixWord, tailWord_2029951, baseEnd_2029951] using wordTrace_append hprefix tailTrace_2029951
  have hstable : (prefixWord ++ tailWord_2029951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029951).length < 2 ^ (prefixWord ++ tailWord_2029951).sum := by decide
  have hdescent : baseEnd_2029951 < baseStart_2029951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029955 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3]
def baseStart_2029955 : Nat := 118140960795 + 2029955 * 2 ^ 59
def prefixEnd_2029955 : Nat := 4983230072969 + 3 ^ 40 * 2029955 * 2
def baseEnd_2029955 : Nat := 1042342621997710525426913

theorem tailTrace_2029955 : CollatzResearch.WordTrace tailWord_2029955 prefixEnd_2029955 1042342621997710525426913 := by
  unfold tailWord_2029955
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038541360827198557811319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49359027573884799038540879 74038541360827198557811319)
  ·
    refine ⟨111057812041240797836716979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74038541360827198557811319 111057812041240797836716979)
    ·
      refine ⟨166586718061861196755075469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111057812041240797836716979 166586718061861196755075469)
      ·
        refine ⟨62470019273197948783153301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166586718061861196755075469 62470019273197948783153301)
        ·
          refine ⟨2928282153431153849210311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62470019273197948783153301 2928282153431153849210311)
          ·
            refine ⟨4392423230146730773815467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928282153431153849210311 4392423230146730773815467)
            ·
              refine ⟨6588634845220096160723201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392423230146730773815467 6588634845220096160723201)
              ·
                refine ⟨4941476133915072120542401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588634845220096160723201 4941476133915072120542401)
                ·
                  refine ⟨3706107100436304090406801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941476133915072120542401 3706107100436304090406801)
                  ·
                    refine ⟨2779580325327228067805101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3706107100436304090406801 2779580325327228067805101)
                    ·
                      refine ⟨1042342621997710525426913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779580325327228067805101 1042342621997710525426913)
                      ·
                        rfl

theorem cell23_2029955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_2029955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029955 prefixEnd_2029955 := by exact prefixLift 2029955
  have htrace : WordTrace (prefixWord ++ tailWord_2029955) baseStart_2029955 baseEnd_2029955 := by
    simpa [prefixWord, tailWord_2029955, baseEnd_2029955] using wordTrace_append hprefix tailTrace_2029955
  have hstable : (prefixWord ++ tailWord_2029955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029955).length < 2 ^ (prefixWord ++ tailWord_2029955).sum := by decide
  have hdescent : baseEnd_2029955 < baseStart_2029955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029968 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3]
def baseStart_2029968 : Nat := 118140960795 + 2029968 * 2 ^ 59
def prefixEnd_2029968 : Nat := 4983230072969 + 3 ^ 40 * 2029968 * 2
def baseEnd_2029968 : Nat := 1042349297246218974564353

theorem tailTrace_2029968 : CollatzResearch.WordTrace tailWord_2029968 prefixEnd_2029968 1042349297246218974564353 := by
  unfold tailWord_2029968
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019507754890050889017279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49359343673186734518689705 37019507754890050889017279)
  ·
    refine ⟨55529261632335076333525919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37019507754890050889017279 55529261632335076333525919)
    ·
      refine ⟨83293892448502614500288879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55529261632335076333525919 83293892448502614500288879)
      ·
        refine ⟨124940838672753921750433319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83293892448502614500288879 124940838672753921750433319)
        ·
          refine ⟨187411258009130882625649979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124940838672753921750433319 187411258009130882625649979)
          ·
            refine ⟨281116887013696323938474969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187411258009130882625649979 281116887013696323938474969)
            ·
              refine ⟨210837665260272242953856227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281116887013696323938474969 210837665260272242953856227)
              ·
                refine ⟨316256497890408364430784341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210837665260272242953856227 316256497890408364430784341)
                ·
                  refine ⟨1853065417326611510336627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 316256497890408364430784341 1853065417326611510336627)
                  ·
                    refine ⟨2779598125989917265504941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1853065417326611510336627 2779598125989917265504941)
                    ·
                      refine ⟨1042349297246218974564353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779598125989917265504941 1042349297246218974564353)
                      ·
                        rfl

theorem cell23_2029968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_2029968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029968 prefixEnd_2029968 := by exact prefixLift 2029968
  have htrace : WordTrace (prefixWord ++ tailWord_2029968) baseStart_2029968 baseEnd_2029968 := by
    simpa [prefixWord, tailWord_2029968, baseEnd_2029968] using wordTrace_append hprefix tailTrace_2029968
  have hstable : (prefixWord ++ tailWord_2029968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029968).length < 2 ^ (prefixWord ++ tailWord_2029968).sum := by decide
  have hdescent : baseEnd_2029968 < baseStart_2029968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030002 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_2030002 : Nat := 118140960795 + 2030002 * 2 ^ 59
def prefixEnd_2030002 : Nat := 4983230072969 + 3 ^ 40 * 2030002 * 2
def baseEnd_2030002 : Nat := 1042366755588471841539197

theorem tailTrace_2030002 : CollatzResearch.WordTrace tailWord_2030002 prefixEnd_2030002 1042366755588471841539197 := by
  unfold tailWord_2030002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510063897914231396193065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49360170394437950389848173 18510063897914231396193065)
  ·
    refine ⟨13882547923435673547144799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18510063897914231396193065 13882547923435673547144799)
    ·
      refine ⟨20823821885153510320717199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13882547923435673547144799 20823821885153510320717199)
      ·
        refine ⟨31235732827730265481075799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20823821885153510320717199 31235732827730265481075799)
        ·
          refine ⟨46853599241595398221613699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31235732827730265481075799 46853599241595398221613699)
          ·
            refine ⟨70280398862393097332420549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46853599241595398221613699 70280398862393097332420549)
            ·
              refine ⟨13177574786698705749828853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70280398862393097332420549 13177574786698705749828853)
              ·
                refine ⟨1235397636253003664046455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13177574786698705749828853 1235397636253003664046455)
                ·
                  refine ⟨1853096454379505496069683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235397636253003664046455 1853096454379505496069683)
                  ·
                    refine ⟨2779644681569258244104525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1853096454379505496069683 2779644681569258244104525)
                    ·
                      refine ⟨1042366755588471841539197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779644681569258244104525 1042366755588471841539197)
                      ·
                        rfl

theorem cell23_2030002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_2030002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030002 prefixEnd_2030002 := by exact prefixLift 2030002
  have htrace : WordTrace (prefixWord ++ tailWord_2030002) baseStart_2030002 baseEnd_2030002 := by
    simpa [prefixWord, tailWord_2030002, baseEnd_2030002] using wordTrace_append hprefix tailTrace_2030002
  have hstable : (prefixWord ++ tailWord_2030002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030002).length < 2 ^ (prefixWord ++ tailWord_2030002).sum := by decide
  have hdescent : baseEnd_2030002 < baseStart_2030002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030011 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_2030011 : Nat := 118140960795 + 2030011 * 2 ^ 59
def prefixEnd_2030011 : Nat := 4983230072969 + 3 ^ 40 * 2030011 * 2
def baseEnd_2030011 : Nat := 1042371376914362306326655

theorem tailTrace_2030011 : CollatzResearch.WordTrace tailWord_2030011 prefixEnd_2030011 1042371376914362306326655 := by
  unfold tailWord_2030011
  simp only [CollatzResearch.WordTrace]
  refine ⟨74040583848624320121849887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49360389232416213414566591 74040583848624320121849887)
  ·
    refine ⟨111060875772936480182774831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74040583848624320121849887 111060875772936480182774831)
    ·
      refine ⟨166591313659404720274162247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111060875772936480182774831 166591313659404720274162247)
      ·
        refine ⟨249886970489107080411243371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166591313659404720274162247 249886970489107080411243371)
        ·
          refine ⟨374830455733660620616865057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249886970489107080411243371 374830455733660620616865057)
          ·
            refine ⟨281122841800245465462648793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374830455733660620616865057 281122841800245465462648793)
            ·
              refine ⟨210842131350184099096986595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281122841800245465462648793 210842131350184099096986595)
              ·
                refine ⟨316263197025276148645479893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210842131350184099096986595 316263197025276148645479893)
                ·
                  refine ⟨7412418680279909733878435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 316263197025276148645479893 7412418680279909733878435)
                  ·
                    refine ⟨11118628020419864600817653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412418680279909733878435 11118628020419864600817653)
                    ·
                      refine ⟨1042371376914362306326655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11118628020419864600817653 1042371376914362306326655)
                      ·
                        rfl

theorem cell23_2030011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_2030011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030011 prefixEnd_2030011 := by exact prefixLift 2030011
  have htrace : WordTrace (prefixWord ++ tailWord_2030011) baseStart_2030011 baseEnd_2030011 := by
    simpa [prefixWord, tailWord_2030011, baseEnd_2030011] using wordTrace_append hprefix tailTrace_2030011
  have hstable : (prefixWord ++ tailWord_2030011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030011).length < 2 ^ (prefixWord ++ tailWord_2030011).sum := by decide
  have hdescent : baseEnd_2030011 < baseStart_2030011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030012 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2030012 : Nat := 118140960795 + 2030012 * 2 ^ 59
def prefixEnd_2030012 : Nat := 4983230072969 + 3 ^ 40 * 2030012 * 2
def baseEnd_2030012 : Nat := 1042371890395016802414151

theorem tailTrace_2030012 : CollatzResearch.WordTrace tailWord_2030012 prefixEnd_2030012 1042371890395016802414151 := by
  unfold tailWord_2030012
  simp only [CollatzResearch.WordTrace]
  refine ⟨37020310160810348646318145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49360413547747131528424193 37020310160810348646318145)
  ·
    refine ⟨27765232620607761484738609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37020310160810348646318145 27765232620607761484738609)
    ·
      refine ⟨20823924465455821113553957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27765232620607761484738609 20823924465455821113553957)
      ·
        refine ⟨3904485837272966458791367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20823924465455821113553957 3904485837272966458791367)
        ·
          refine ⟨5856728755909449688187051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904485837272966458791367 5856728755909449688187051)
          ·
            refine ⟨8785093133864174532280577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856728755909449688187051 8785093133864174532280577)
            ·
              refine ⟨6588819850398130899210433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785093133864174532280577 6588819850398130899210433)
              ·
                refine ⟨4941614887798598174407825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588819850398130899210433 4941614887798598174407825)
                ·
                  refine ⟨3706211165848948630805869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941614887798598174407825 3706211165848948630805869)
                  ·
                    refine ⟨1389829187193355736552201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706211165848948630805869 1389829187193355736552201)
                    ·
                      refine ⟨1042371890395016802414151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389829187193355736552201 1042371890395016802414151)
                      ·
                        rfl

theorem cell23_2030012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2030012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030012 prefixEnd_2030012 := by exact prefixLift 2030012
  have htrace : WordTrace (prefixWord ++ tailWord_2030012) baseStart_2030012 baseEnd_2030012 := by
    simpa [prefixWord, tailWord_2030012, baseEnd_2030012] using wordTrace_append hprefix tailTrace_2030012
  have hstable : (prefixWord ++ tailWord_2030012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030012).length < 2 ^ (prefixWord ++ tailWord_2030012).sum := by decide
  have hdescent : baseEnd_2030012 < baseStart_2030012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030042 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_2030042 : Nat := 118140960795 + 2030042 * 2 ^ 59
def prefixEnd_2030042 : Nat := 4983230072969 + 3 ^ 40 * 2030042 * 2
def baseEnd_2030042 : Nat := 1042387294814651685039013

theorem tailTrace_2030042 : CollatzResearch.WordTrace tailWord_2030042 prefixEnd_2030042 1042387294814651685039013 := by
  unfold tailWord_2030042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510428627878003104057095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49361143007674674944152253 18510428627878003104057095)
  ·
    refine ⟨27765642941817004656085643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18510428627878003104057095 27765642941817004656085643)
    ·
      refine ⟨41648464412725506984128465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27765642941817004656085643 41648464412725506984128465)
      ·
        refine ⟨31236348309544130238096349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41648464412725506984128465 31236348309544130238096349)
        ·
          refine ⟨11713630616079048839286131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31236348309544130238096349 11713630616079048839286131)
          ·
            refine ⟨17570445924118573258929197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713630616079048839286131 17570445924118573258929197)
            ·
              refine ⟨6588917221544464972098449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17570445924118573258929197 6588917221544464972098449)
              ·
                refine ⟨4941687916158348729073837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588917221544464972098449 4941687916158348729073837)
                ·
                  refine ⟨1853132968559380773402689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4941687916158348729073837 1853132968559380773402689)
                  ·
                    refine ⟨1389849726419535580052017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853132968559380773402689 1389849726419535580052017)
                    ·
                      refine ⟨1042387294814651685039013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389849726419535580052017 1042387294814651685039013)
                      ·
                        rfl

theorem cell23_2030042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_2030042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030042 prefixEnd_2030042 := by exact prefixLift 2030042
  have htrace : WordTrace (prefixWord ++ tailWord_2030042) baseStart_2030042 baseEnd_2030042 := by
    simpa [prefixWord, tailWord_2030042, baseEnd_2030042] using wordTrace_append hprefix tailTrace_2030042
  have hstable : (prefixWord ++ tailWord_2030042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030042).length < 2 ^ (prefixWord ++ tailWord_2030042).sum := by decide
  have hdescent : baseEnd_2030042 < baseStart_2030042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030045 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2030045 : Nat := 118140960795 + 2030045 * 2 ^ 59
def prefixEnd_2030045 : Nat := 4983230072969 + 3 ^ 40 * 2030045 * 2
def baseEnd_2030045 : Nat := 1042388835256615173301499

theorem tailTrace_2030045 : CollatzResearch.WordTrace tailWord_2030045 prefixEnd_2030045 1042388835256615173301499 := by
  unfold tailWord_2030045
  simp only [CollatzResearch.WordTrace]
  refine ⟨74041823930501143928587589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49361215953667429285725059 74041823930501143928587589)
  ·
    refine ⟨13882841986968964486610173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74041823930501143928587589 13882841986968964486610173)
    ·
      refine ⟨5206065745113361682478815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13882841986968964486610173 5206065745113361682478815)
      ·
        refine ⟨7809098617670042523718223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206065745113361682478815 7809098617670042523718223)
        ·
          refine ⟨11713647926505063785577335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809098617670042523718223 11713647926505063785577335)
          ·
            refine ⟨17570471889757595678366003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713647926505063785577335 17570471889757595678366003)
            ·
              refine ⟨26355707834636393517549005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570471889757595678366003 26355707834636393517549005)
              ·
                refine ⟨9883390437988647569080877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26355707834636393517549005 9883390437988647569080877)
                ·
                  refine ⟨3706271414245742838405329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9883390437988647569080877 3706271414245742838405329)
                  ·
                    refine ⟨2779703560684307128803997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3706271414245742838405329 2779703560684307128803997)
                    ·
                      refine ⟨1042388835256615173301499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779703560684307128803997 1042388835256615173301499)
                      ·
                        rfl

theorem cell23_2030045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2030045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030045 prefixEnd_2030045 := by exact prefixLift 2030045
  have htrace : WordTrace (prefixWord ++ tailWord_2030045) baseStart_2030045 baseEnd_2030045 := by
    simpa [prefixWord, tailWord_2030045, baseEnd_2030045] using wordTrace_append hprefix tailTrace_2030045
  have hstable : (prefixWord ++ tailWord_2030045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030045).length < 2 ^ (prefixWord ++ tailWord_2030045).sum := by decide
  have hdescent : baseEnd_2030045 < baseStart_2030045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030048 : List Nat := [2, 1, 1, 3, 1, 1, 7, 7]
def baseStart_2030048 : Nat := 118140960795 + 2030048 * 2 ^ 59
def prefixEnd_2030048 : Nat := 4983230072969 + 3 ^ 40 * 2030048 * 2
def baseEnd_2030048 : Nat := 38607050951799209687555

theorem tailTrace_2030048 : CollatzResearch.WordTrace tailWord_2030048 prefixEnd_2030048 38607050951799209687555 := by
  unfold tailWord_2030048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37020966674745137720473399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49361288899660183627297865 37020966674745137720473399)
  ·
    refine ⟨55531450012117706580710099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37020966674745137720473399 55531450012117706580710099)
    ·
      refine ⟨83297175018176559871065149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55531450012117706580710099 83297175018176559871065149)
      ·
        refine ⟨31236440631816209951649431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83297175018176559871065149 31236440631816209951649431)
        ·
          refine ⟨46854660947724314927474147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31236440631816209951649431 46854660947724314927474147)
          ·
            refine ⟨70281991421586472391211221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46854660947724314927474147 70281991421586472391211221)
            ·
              refine ⟨1647234173943432946669013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70281991421586472391211221 1647234173943432946669013)
              ·
                refine ⟨38607050951799209687555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1647234173943432946669013 38607050951799209687555)
                ·
                  rfl

theorem cell23_2030048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 7].length) (baseStart_2030048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030048 prefixEnd_2030048 := by exact prefixLift 2030048
  have htrace : WordTrace (prefixWord ++ tailWord_2030048) baseStart_2030048 baseEnd_2030048 := by
    simpa [prefixWord, tailWord_2030048, baseEnd_2030048] using wordTrace_append hprefix tailTrace_2030048
  have hstable : (prefixWord ++ tailWord_2030048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030048).length < 2 ^ (prefixWord ++ tailWord_2030048).sum := by decide
  have hdescent : baseEnd_2030048 < baseStart_2030048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030059 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 1, 2, 2]
def baseStart_2030059 : Nat := 118140960795 + 2030059 * 2 ^ 59
def prefixEnd_2030059 : Nat := 4983230072969 + 3 ^ 40 * 2030059 * 2
def baseEnd_2030059 : Nat := 1042396023985778118526435

theorem tailTrace_2030059 : CollatzResearch.WordTrace tailWord_2030059 prefixEnd_2030059 1042396023985778118526435 := by
  unfold tailWord_2030059
  simp only [CollatzResearch.WordTrace]
  refine ⟨74042334552450424319597231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49361556368300282879731487 74042334552450424319597231)
  ·
    refine ⟨111063501828675636479395847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74042334552450424319597231 111063501828675636479395847)
    ·
      refine ⟨166595252743013454719093771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111063501828675636479395847 166595252743013454719093771)
      ·
        refine ⟨249892879114520182078640657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166595252743013454719093771 249892879114520182078640657)
        ·
          refine ⟨187419659335890136558980493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249892879114520182078640657 187419659335890136558980493)
          ·
            refine ⟨70282372250958801209617685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187419659335890136558980493 70282372250958801209617685)
            ·
              refine ⟨3294486199263693806700829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70282372250958801209617685 3294486199263693806700829)
              ·
                refine ⟨1235432324723885177512811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3294486199263693806700829 1235432324723885177512811)
                ·
                  refine ⟨1853148487085827766269217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235432324723885177512811 1853148487085827766269217)
                  ·
                    refine ⟨1389861365314370824701913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853148487085827766269217 1389861365314370824701913)
                    ·
                      refine ⟨1042396023985778118526435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389861365314370824701913 1042396023985778118526435)
                      ·
                        rfl

theorem cell23_2030059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 2, 2].length) (baseStart_2030059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030059 prefixEnd_2030059 := by exact prefixLift 2030059
  have htrace : WordTrace (prefixWord ++ tailWord_2030059) baseStart_2030059 baseEnd_2030059 := by
    simpa [prefixWord, tailWord_2030059, baseEnd_2030059] using wordTrace_append hprefix tailTrace_2030059
  have hstable : (prefixWord ++ tailWord_2030059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030059).length < 2 ^ (prefixWord ++ tailWord_2030059).sum := by decide
  have hdescent : baseEnd_2030059 < baseStart_2030059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030062 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2030062 : Nat := 118140960795 + 2030062 * 2 ^ 59
def prefixEnd_2030062 : Nat := 4983230072969 + 3 ^ 40 * 2030062 * 2
def baseEnd_2030062 : Nat := 1042397564427741606788921

theorem tailTrace_2030062 : CollatzResearch.WordTrace tailWord_2030062 prefixEnd_2030062 1042397564427741606788921 := by
  unfold tailWord_2030062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255305496429944478994555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49361629314293037221304293 9255305496429944478994555)
  ·
    refine ⟨13882958244644916718491833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255305496429944478994555 13882958244644916718491833)
    ·
      refine ⟨10412218683483687538868875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13882958244644916718491833 10412218683483687538868875)
      ·
        refine ⟨15618328025225531308303313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10412218683483687538868875 15618328025225531308303313)
        ·
          refine ⟨11713746018919148481227485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15618328025225531308303313 11713746018919148481227485)
          ·
            refine ⟨4392654757094680680460307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11713746018919148481227485 4392654757094680680460307)
            ·
              refine ⟨6588982135642021020690461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392654757094680680460307 6588982135642021020690461)
              ·
                refine ⟨2470868300865757882758923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6588982135642021020690461 2470868300865757882758923)
                ·
                  refine ⟨3706302451298636824138385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470868300865757882758923 3706302451298636824138385)
                  ·
                    refine ⟨2779726838473977618103789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3706302451298636824138385 2779726838473977618103789)
                    ·
                      refine ⟨1042397564427741606788921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779726838473977618103789 1042397564427741606788921)
                      ·
                        rfl

theorem cell23_2030062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2030062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030062 prefixEnd_2030062 := by exact prefixLift 2030062
  have htrace : WordTrace (prefixWord ++ tailWord_2030062) baseStart_2030062 baseEnd_2030062 := by
    simpa [prefixWord, tailWord_2030062, baseEnd_2030062] using wordTrace_append hprefix tailTrace_2030062
  have hstable : (prefixWord ++ tailWord_2030062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030062).length < 2 ^ (prefixWord ++ tailWord_2030062).sum := by decide
  have hdescent : baseEnd_2030062 < baseStart_2030062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030085 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_2030085 : Nat := 118140960795 + 2030085 * 2 ^ 59
def prefixEnd_2030085 : Nat := 4983230072969 + 3 ^ 40 * 2030085 * 2
def baseEnd_2030085 : Nat := 1042409374482795016801315

theorem tailTrace_2030085 : CollatzResearch.WordTrace tailWord_2030085 prefixEnd_2030085 1042409374482795016801315 := by
  unfold tailWord_2030085
  simp only [CollatzResearch.WordTrace]
  refine ⟨74043282850356230760043709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49362188566904153840029139 74043282850356230760043709)
  ·
    refine ⟨27766231068883586535016391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74043282850356230760043709 27766231068883586535016391)
    ·
      refine ⟨41649346603325379802524587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27766231068883586535016391 41649346603325379802524587)
      ·
        refine ⟨62474019904988069703786881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41649346603325379802524587 62474019904988069703786881)
        ·
          refine ⟨46855514928741052277840161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62474019904988069703786881 46855514928741052277840161)
          ·
            refine ⟨35141636196555789208380121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46855514928741052277840161 35141636196555789208380121)
            ·
              refine ⟨26356227147416841906285091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35141636196555789208380121 26356227147416841906285091)
              ·
                refine ⟨39534340721125262859427637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26356227147416841906285091 39534340721125262859427637)
                ·
                  refine ⟨3706344442605493393071341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39534340721125262859427637 3706344442605493393071341)
                  ·
                    refine ⟨1389879165977060022401753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706344442605493393071341 1389879165977060022401753)
                    ·
                      refine ⟨1042409374482795016801315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389879165977060022401753 1042409374482795016801315)
                      ·
                        rfl

theorem cell23_2030085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_2030085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030085 prefixEnd_2030085 := by exact prefixLift 2030085
  have htrace : WordTrace (prefixWord ++ tailWord_2030085) baseStart_2030085 baseEnd_2030085 := by
    simpa [prefixWord, tailWord_2030085, baseEnd_2030085] using wordTrace_append hprefix tailTrace_2030085
  have hstable : (prefixWord ++ tailWord_2030085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030085).length < 2 ^ (prefixWord ++ tailWord_2030085).sum := by decide
  have hdescent : baseEnd_2030085 < baseStart_2030085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030086 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2030086 : Nat := 118140960795 + 2030086 * 2 ^ 59
def prefixEnd_2030086 : Nat := 4983230072969 + 3 ^ 40 * 2030086 * 2
def baseEnd_2030086 : Nat := 347469962654483170962937

theorem tailTrace_2030086 : CollatzResearch.WordTrace tailWord_2030086 prefixEnd_2030086 347469962654483170962937 := by
  unfold tailWord_2030086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313853728854768997838441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49362212882235071953886741 2313853728854768997838441)
  ·
    refine ⟨1735390296641076748378831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2313853728854768997838441 1735390296641076748378831)
    ·
      refine ⟨2603085444961615122568247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735390296641076748378831 2603085444961615122568247)
      ·
        refine ⟨3904628167442422683852371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603085444961615122568247 3904628167442422683852371)
        ·
          refine ⟨5856942251163634025778557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904628167442422683852371 5856942251163634025778557)
          ·
            refine ⟨2196353344186362759666959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5856942251163634025778557 2196353344186362759666959)
            ·
              refine ⟨3294530016279544139500439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196353344186362759666959 3294530016279544139500439)
              ·
                refine ⟨4941795024419316209250659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294530016279544139500439 4941795024419316209250659)
                ·
                  refine ⟨7412692536628974313875989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941795024419316209250659 7412692536628974313875989)
                  ·
                    refine ⟨347469962654483170962937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7412692536628974313875989 347469962654483170962937)
                    ·
                      rfl

theorem cell23_2030086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2030086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030086 prefixEnd_2030086 := by exact prefixLift 2030086
  have htrace : WordTrace (prefixWord ++ tailWord_2030086) baseStart_2030086 baseEnd_2030086 := by
    simpa [prefixWord, tailWord_2030086, baseEnd_2030086] using wordTrace_append hprefix tailTrace_2030086
  have hstable : (prefixWord ++ tailWord_2030086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030086).length < 2 ^ (prefixWord ++ tailWord_2030086).sum := by decide
  have hdescent : baseEnd_2030086 < baseStart_2030086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030092 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_2030092 : Nat := 118140960795 + 2030092 * 2 ^ 59
def prefixEnd_2030092 : Nat := 4983230072969 + 3 ^ 40 * 2030092 * 2
def baseEnd_2030092 : Nat := 1042412968847376489413783

theorem tailTrace_2030092 : CollatzResearch.WordTrace tailWord_2030092 prefixEnd_2030092 1042412968847376489413783 := by
  unfold tailWord_2030092
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021769080665435477774265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49362358774220580637032353 37021769080665435477774265)
  ·
    refine ⟨27766326810499076608330699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37021769080665435477774265 27766326810499076608330699)
    ·
      refine ⟨41649490215748614912496049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27766326810499076608330699 41649490215748614912496049)
      ·
        refine ⟨31237117661811461184372037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41649490215748614912496049 31237117661811461184372037)
        ·
          refine ⟨5856959561589648972069757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31237117661811461184372037 5856959561589648972069757)
          ·
            refine ⟨2196359835596118364526159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5856959561589648972069757 2196359835596118364526159)
            ·
              refine ⟨3294539753394177546789239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196359835596118364526159 3294539753394177546789239)
              ·
                refine ⟨4941809630091266320183859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294539753394177546789239 4941809630091266320183859)
                ·
                  refine ⟨7412714445136899480275789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941809630091266320183859 7412714445136899480275789)
                  ·
                    refine ⟨2779767916926337305103421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7412714445136899480275789 2779767916926337305103421)
                    ·
                      refine ⟨1042412968847376489413783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2779767916926337305103421 1042412968847376489413783)
                      ·
                        rfl

theorem cell23_2030092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_2030092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030092 prefixEnd_2030092 := by exact prefixLift 2030092
  have htrace : WordTrace (prefixWord ++ tailWord_2030092) baseStart_2030092 baseEnd_2030092 := by
    simpa [prefixWord, tailWord_2030092, baseEnd_2030092] using wordTrace_append hprefix tailTrace_2030092
  have hstable : (prefixWord ++ tailWord_2030092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030092).length < 2 ^ (prefixWord ++ tailWord_2030092).sum := by decide
  have hdescent : baseEnd_2030092 < baseStart_2030092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030128 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_2030128 : Nat := 118140960795 + 2030128 * 2 ^ 59
def prefixEnd_2030128 : Nat := 4983230072969 + 3 ^ 40 * 2030128 * 2
def baseEnd_2030128 : Nat := 1042431454150938348563617

theorem tailTrace_2030128 : CollatzResearch.WordTrace tailWord_2030128 prefixEnd_2030128 1042431454150938348563617 := by
  unfold tailWord_2030128
  simp only [CollatzResearch.WordTrace]
  refine ⟨37022425594600224551929519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49363234126133632735906025 37022425594600224551929519)
  ·
    refine ⟨55533638391900336827894279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37022425594600224551929519 55533638391900336827894279)
    ·
      refine ⟨83300457587850505241841419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55533638391900336827894279 83300457587850505241841419)
      ·
        refine ⟨124950686381775757862762129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83300457587850505241841419 124950686381775757862762129)
        ·
          refine ⟨93713014786331818397071597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124950686381775757862762129 93713014786331818397071597)
          ·
            refine ⟨35142380544874431898901849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93713014786331818397071597 35142380544874431898901849)
            ·
              refine ⟨26356785408655823924176387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35142380544874431898901849 26356785408655823924176387)
              ·
                refine ⟨39535178112983735886264581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26356785408655823924176387 39535178112983735886264581)
                ·
                  refine ⟨7412845896184450478674609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39535178112983735886264581 7412845896184450478674609)
                  ·
                    refine ⟨5559634422138337859005957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7412845896184450478674609 5559634422138337859005957)
                    ·
                      refine ⟨1042431454150938348563617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5559634422138337859005957 1042431454150938348563617)
                      ·
                        rfl

theorem cell23_2030128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_2030128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030128 prefixEnd_2030128 := by exact prefixLift 2030128
  have htrace : WordTrace (prefixWord ++ tailWord_2030128) baseStart_2030128 baseEnd_2030128 := by
    simpa [prefixWord, tailWord_2030128, baseEnd_2030128] using wordTrace_append hprefix tailTrace_2030128
  have hstable : (prefixWord ++ tailWord_2030128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030128).length < 2 ^ (prefixWord ++ tailWord_2030128).sum := by decide
  have hdescent : baseEnd_2030128 < baseStart_2030128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030149 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_2030149 : Nat := 118140960795 + 2030149 * 2 ^ 59
def prefixEnd_2030149 : Nat := 4983230072969 + 3 ^ 40 * 2030149 * 2
def baseEnd_2030149 : Nat := 1042442237244682766401021

theorem tailTrace_2030149 : CollatzResearch.WordTrace tailWord_2030149 prefixEnd_2030149 1042442237244682766401021 := by
  unfold tailWord_2030149
  simp only [CollatzResearch.WordTrace]
  refine ⟨74045617122124369690373501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49363744748082913126915667 74045617122124369690373501)
  ·
    refine ⟨27767106420796638633890063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74045617122124369690373501 27767106420796638633890063)
    ·
      refine ⟨41650659631194957950835095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27767106420796638633890063 41650659631194957950835095)
      ·
        refine ⟨62475989446792436926252643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41650659631194957950835095 62475989446792436926252643)
        ·
          refine ⟨93713984170188655389378965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62475989446792436926252643 93713984170188655389378965)
          ·
            refine ⟨4392843007977593221377139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93713984170188655389378965 4392843007977593221377139)
            ·
              refine ⟨6589264511966389832065709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392843007977593221377139 6589264511966389832065709)
              ·
                refine ⟨2470974191987396187024641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6589264511966389832065709 2470974191987396187024641)
                ·
                  refine ⟨1853230643990547140268481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2470974191987396187024641 1853230643990547140268481)
                  ·
                    refine ⟨1389922982992910355201361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853230643990547140268481 1389922982992910355201361)
                    ·
                      refine ⟨1042442237244682766401021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389922982992910355201361 1042442237244682766401021)
                      ·
                        rfl

theorem cell23_2030149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_2030149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030149 prefixEnd_2030149 := by exact prefixLift 2030149
  have htrace : WordTrace (prefixWord ++ tailWord_2030149) baseStart_2030149 baseEnd_2030149 := by
    simpa [prefixWord, tailWord_2030149, baseEnd_2030149] using wordTrace_append hprefix tailTrace_2030149
  have hstable : (prefixWord ++ tailWord_2030149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030149).length < 2 ^ (prefixWord ++ tailWord_2030149).sum := by decide
  have hdescent : baseEnd_2030149 < baseStart_2030149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030168 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_2030168 : Nat := 118140960795 + 2030168 * 2 ^ 59
def prefixEnd_2030168 : Nat := 4983230072969 + 3 ^ 40 * 2030168 * 2
def baseEnd_2030168 : Nat := 347483997792372730687811

theorem tailTrace_2030168 : CollatzResearch.WordTrace tailWord_2030168 prefixEnd_2030168 347483997792372730687811 := by
  unfold tailWord_2030168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37023155054527767967657579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49364206739370357290210105 37023155054527767967657579)
  ·
    refine ⟨55534732581791651951486369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37023155054527767967657579 55534732581791651951486369)
    ·
      refine ⟨41651049436343738963614777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55534732581791651951486369 41651049436343738963614777)
      ·
        refine ⟨31238287077257804222711083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41651049436343738963614777 31238287077257804222711083)
        ·
          refine ⟨46857430615886706334066625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238287077257804222711083 46857430615886706334066625)
          ·
            refine ⟨35143072961915029750549969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46857430615886706334066625 35143072961915029750549969)
            ·
              refine ⟨26357304721436272312912477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35143072961915029750549969 26357304721436272312912477)
              ·
                refine ⟨9883989270538602117342179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26357304721436272312912477 9883989270538602117342179)
                ·
                  refine ⟨14825983905807903176013269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9883989270538602117342179 14825983905807903176013269)
                  ·
                    refine ⟨347483997792372730687811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14825983905807903176013269 347483997792372730687811)
                    ·
                      rfl

theorem cell23_2030168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_2030168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030168 prefixEnd_2030168 := by exact prefixLift 2030168
  have htrace : WordTrace (prefixWord ++ tailWord_2030168) baseStart_2030168 baseEnd_2030168 := by
    simpa [prefixWord, tailWord_2030168, baseEnd_2030168] using wordTrace_append hprefix tailTrace_2030168
  have hstable : (prefixWord ++ tailWord_2030168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030168).length < 2 ^ (prefixWord ++ tailWord_2030168).sum := by decide
  have hdescent : baseEnd_2030168 < baseStart_2030168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030175 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 5, 2]
def baseStart_2030175 : Nat := 118140960795 + 2030175 * 2 ^ 59
def prefixEnd_2030175 : Nat := 4983230072969 + 3 ^ 40 * 2030175 * 2
def baseEnd_2030175 : Nat := 1042455587741699664675901

theorem tailTrace_2030175 : CollatzResearch.WordTrace tailWord_2030175 prefixEnd_2030175 1042455587741699664675901 := by
  unfold tailWord_2030175
  simp only [CollatzResearch.WordTrace]
  refine ⟨74046565420030176130819979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49364376946686784087213319 74046565420030176130819979)
  ·
    refine ⟨111069848130045264196229969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74046565420030176130819979 111069848130045264196229969)
    ·
      refine ⟨83302386097533948147172477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111069848130045264196229969 83302386097533948147172477)
      ·
        refine ⟨31238394786575230555189679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83302386097533948147172477 31238394786575230555189679)
        ·
          refine ⟨46857592179862845832784519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238394786575230555189679 46857592179862845832784519)
          ·
            refine ⟨70286388269794268749176779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46857592179862845832784519 70286388269794268749176779)
            ·
              refine ⟨105429582404691403123765169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70286388269794268749176779 105429582404691403123765169)
              ·
                refine ⟨79072186803518552342823877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105429582404691403123765169 79072186803518552342823877)
                ·
                  refine ⟨14826035025659728564279477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79072186803518552342823877 14826035025659728564279477)
                  ·
                    refine ⟨1389940783655599552901201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14826035025659728564279477 1389940783655599552901201)
                    ·
                      refine ⟨1042455587741699664675901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389940783655599552901201 1042455587741699664675901)
                      ·
                        rfl

theorem cell23_2030175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_2030175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030175 prefixEnd_2030175 := by exact prefixLift 2030175
  have htrace : WordTrace (prefixWord ++ tailWord_2030175) baseStart_2030175 baseEnd_2030175 := by
    simpa [prefixWord, tailWord_2030175, baseEnd_2030175] using wordTrace_append hprefix tailTrace_2030175
  have hstable : (prefixWord ++ tailWord_2030175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030175).length < 2 ^ (prefixWord ++ tailWord_2030175).sum := by decide
  have hdescent : baseEnd_2030175 < baseStart_2030175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030189 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2030189 : Nat := 118140960795 + 2030189 * 2 ^ 59
def prefixEnd_2030189 : Nat := 4983230072969 + 3 ^ 40 * 2030189 * 2
def baseEnd_2030189 : Nat := 115829197385651401100093

theorem tailTrace_2030189 : CollatzResearch.WordTrace tailWord_2030189 prefixEnd_2030189 115829197385651401100093 := by
  unfold tailWord_2030189
  simp only [CollatzResearch.WordTrace]
  refine ⟨74047076041979456521829621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49364717361319637681219747 74047076041979456521829621)
  ·
    refine ⟨6941913378935574048921527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74047076041979456521829621 6941913378935574048921527)
    ·
      refine ⟨10412870068403361073382291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6941913378935574048921527 10412870068403361073382291)
      ·
        refine ⟨15619305102605041610073437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10412870068403361073382291 15619305102605041610073437)
        ·
          refine ⟨5857239413476890603777539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15619305102605041610073437 5857239413476890603777539)
          ·
            refine ⟨8785859120215335905666309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857239413476890603777539 8785859120215335905666309)
            ·
              refine ⟨1647348585040375482312433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8785859120215335905666309 1647348585040375482312433)
              ·
                refine ⟨1235511438780281611734325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647348585040375482312433 1235511438780281611734325)
                ·
                  refine ⟨115829197385651401100093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235511438780281611734325 115829197385651401100093)
                  ·
                    rfl

theorem cell23_2030189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2030189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030189 prefixEnd_2030189 := by exact prefixLift 2030189
  have htrace : WordTrace (prefixWord ++ tailWord_2030189) baseStart_2030189 baseEnd_2030189 := by
    simpa [prefixWord, tailWord_2030189, baseEnd_2030189] using wordTrace_append hprefix tailTrace_2030189
  have hstable : (prefixWord ++ tailWord_2030189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030189).length < 2 ^ (prefixWord ++ tailWord_2030189).sum := by decide
  have hdescent : baseEnd_2030189 < baseStart_2030189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030222 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2030222 : Nat := 118140960795 + 2030222 * 2 ^ 59
def prefixEnd_2030222 : Nat := 4983230072969 + 3 ^ 40 * 2030222 * 2
def baseEnd_2030222 : Nat := 1042479721332460980788185

theorem tailTrace_2030222 : CollatzResearch.WordTrace tailWord_2030222 prefixEnd_2030222 1042479721332460980788185 := by
  unfold tailWord_2030222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256034956357487894722615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49365519767239935438520613 9256034956357487894722615)
  ·
    refine ⟨13884052434536231842083923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9256034956357487894722615 13884052434536231842083923)
    ·
      refine ⟨20826078651804347763125885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884052434536231842083923 20826078651804347763125885)
      ·
        refine ⟨7809779494426630411172207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20826078651804347763125885 7809779494426630411172207)
        ·
          refine ⟨11714669241639945616758311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809779494426630411172207 11714669241639945616758311)
          ·
            refine ⟨17572003862459918425137467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714669241639945616758311 17572003862459918425137467)
            ·
              refine ⟨26358005793689877637706201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17572003862459918425137467 26358005793689877637706201)
              ·
                refine ⟨19768504345267408228279651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26358005793689877637706201 19768504345267408228279651)
                ·
                  refine ⟨29652756517901112342419477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19768504345267408228279651 29652756517901112342419477)
                  ·
                    refine ⟨1389972961776614641050913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29652756517901112342419477 1389972961776614641050913)
                    ·
                      refine ⟨1042479721332460980788185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389972961776614641050913 1042479721332460980788185)
                      ·
                        rfl

theorem cell23_2030222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2030222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030222 prefixEnd_2030222 := by exact prefixLift 2030222
  have htrace : WordTrace (prefixWord ++ tailWord_2030222) baseStart_2030222 baseEnd_2030222 := by
    simpa [prefixWord, tailWord_2030222, baseEnd_2030222] using wordTrace_append hprefix tailTrace_2030222
  have hstable : (prefixWord ++ tailWord_2030222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030222).length < 2 ^ (prefixWord ++ tailWord_2030222).sum := by decide
  have hdescent : baseEnd_2030222 < baseStart_2030222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030315 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3]
def baseStart_2030315 : Nat := 118140960795 + 2030315 * 2 ^ 59
def prefixEnd_2030315 : Nat := 4983230072969 + 3 ^ 40 * 2030315 * 2
def baseEnd_2030315 : Nat := 1042527475033329116925257

theorem tailTrace_2030315 : CollatzResearch.WordTrace tailWord_2030315 prefixEnd_2030315 1042527475033329116925257 := by
  unfold tailWord_2030315
  simp only [CollatzResearch.WordTrace]
  refine ⟨74051671639522980040916399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49367781093015320027277599 74051671639522980040916399)
  ·
    refine ⟨111077507459284470061374599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74051671639522980040916399 111077507459284470061374599)
    ·
      refine ⟨166616261188926705092061899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111077507459284470061374599 166616261188926705092061899)
      ·
        refine ⟨249924391783390057638092849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166616261188926705092061899 249924391783390057638092849)
        ·
          refine ⟨187443293837542543228569637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249924391783390057638092849 187443293837542543228569637)
          ·
            refine ⟨35145617594539226855356807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187443293837542543228569637 35145617594539226855356807)
            ·
              refine ⟨52718426391808840283035211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35145617594539226855356807 52718426391808840283035211)
              ·
                refine ⟨79077639587713260424552817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52718426391808840283035211 79077639587713260424552817)
                ·
                  refine ⟨59308229690784945318414613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79077639587713260424552817 59308229690784945318414613)
                  ·
                    refine ⟨2780073266755544311800685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59308229690784945318414613 2780073266755544311800685)
                    ·
                      refine ⟨1042527475033329116925257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780073266755544311800685 1042527475033329116925257)
                      ·
                        rfl

theorem cell23_2030315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3].length) (baseStart_2030315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030315 prefixEnd_2030315 := by exact prefixLift 2030315
  have htrace : WordTrace (prefixWord ++ tailWord_2030315) baseStart_2030315 baseEnd_2030315 := by
    simpa [prefixWord, tailWord_2030315, baseEnd_2030315] using wordTrace_append hprefix tailTrace_2030315
  have hstable : (prefixWord ++ tailWord_2030315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030315).length < 2 ^ (prefixWord ++ tailWord_2030315).sum := by decide
  have hdescent : baseEnd_2030315 < baseStart_2030315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030329 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 3, 2, 2]
def baseStart_2030329 : Nat := 118140960795 + 2030329 * 2 ^ 59
def prefixEnd_2030329 : Nat := 4983230072969 + 3 ^ 40 * 2030329 * 2
def baseEnd_2030329 : Nat := 1042534663762492062150193

theorem tailTrace_2030329 : CollatzResearch.WordTrace tailWord_2030329 prefixEnd_2030329 1042534663762492062150193 := by
  unfold tailWord_2030329
  simp only [CollatzResearch.WordTrace]
  refine ⟨74052182261472260431926041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49368121507648173621284027 74052182261472260431926041)
  ·
    refine ⟨55539136696104195323944531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74052182261472260431926041 55539136696104195323944531)
    ·
      refine ⟨83308705044156292985916797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55539136696104195323944531 83308705044156292985916797)
      ·
        refine ⟨31240764391558609869718799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83308705044156292985916797 31240764391558609869718799)
        ·
          refine ⟨46861146587337914804578199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31240764391558609869718799 46861146587337914804578199)
          ·
            refine ⟨70291719881006872206867299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46861146587337914804578199 70291719881006872206867299)
            ·
              refine ⟨105437579821510308310300949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70291719881006872206867299 105437579821510308310300949)
              ·
                refine ⟨4942386554133295702045357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105437579821510308310300949 4942386554133295702045357)
                ·
                  refine ⟨1853394957799985888267009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4942386554133295702045357 1853394957799985888267009)
                  ·
                    refine ⟨1390046218349989416200257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853394957799985888267009 1390046218349989416200257)
                    ·
                      refine ⟨1042534663762492062150193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390046218349989416200257 1042534663762492062150193)
                      ·
                        rfl

theorem cell23_2030329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_2030329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030329 prefixEnd_2030329 := by exact prefixLift 2030329
  have htrace : WordTrace (prefixWord ++ tailWord_2030329) baseStart_2030329 baseEnd_2030329 := by
    simpa [prefixWord, tailWord_2030329, baseEnd_2030329] using wordTrace_append hprefix tailTrace_2030329
  have hstable : (prefixWord ++ tailWord_2030329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030329).length < 2 ^ (prefixWord ++ tailWord_2030329).sum := by decide
  have hdescent : baseEnd_2030329 < baseStart_2030329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030362 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_2030362 : Nat := 118140960795 + 2030362 * 2 ^ 59
def prefixEnd_2030362 : Nat := 4983230072969 + 3 ^ 40 * 2030362 * 2
def baseEnd_2030362 : Nat := 1042551608624090433037541

theorem tailTrace_2030362 : CollatzResearch.WordTrace tailWord_2030362 prefixEnd_2030362 1042551608624090433037541 := by
  unfold tailWord_2030362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18513346467588176766969335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49368923913568471378584893 18513346467588176766969335)
  ·
    refine ⟨27770019701382265150454003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18513346467588176766969335 27770019701382265150454003)
    ·
      refine ⟨41655029552073397725681005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27770019701382265150454003 41655029552073397725681005)
      ·
        refine ⟨15620636082027524147130377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41655029552073397725681005 15620636082027524147130377)
        ·
          refine ⟨11715477061520643110347783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15620636082027524147130377 11715477061520643110347783)
          ·
            refine ⟨17573215592280964665521675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715477061520643110347783 17573215592280964665521675)
            ·
              refine ⟨26359823388421446998282513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573215592280964665521675 26359823388421446998282513)
              ·
                refine ⟨19769867541316085248711885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26359823388421446998282513 19769867541316085248711885)
                ·
                  refine ⟨7413700327993531968266957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19769867541316085248711885 7413700327993531968266957)
                  ·
                    refine ⟨2780137622997574488100109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7413700327993531968266957 2780137622997574488100109)
                    ·
                      refine ⟨1042551608624090433037541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780137622997574488100109 1042551608624090433037541)
                      ·
                        rfl

theorem cell23_2030362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_2030362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030362 prefixEnd_2030362 := by exact prefixLift 2030362
  have htrace : WordTrace (prefixWord ++ tailWord_2030362) baseStart_2030362 baseEnd_2030362 := by
    simpa [prefixWord, tailWord_2030362, baseEnd_2030362] using wordTrace_append hprefix tailTrace_2030362
  have hstable : (prefixWord ++ tailWord_2030362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030362).length < 2 ^ (prefixWord ++ tailWord_2030362).sum := by decide
  have hdescent : baseEnd_2030362 < baseStart_2030362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030412 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_2030412 : Nat := 118140960795 + 2030412 * 2 ^ 59
def prefixEnd_2030412 : Nat := 4983230072969 + 3 ^ 40 * 2030412 * 2
def baseEnd_2030412 : Nat := 347525760885605079137437

theorem tailTrace_2030412 : CollatzResearch.WordTrace tailWord_2030412 prefixEnd_2030412 347525760885605079137437 := by
  unfold tailWord_2030412
  simp only [CollatzResearch.WordTrace]
  refine ⟨37027604760085782803598745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49370139680114377071464993 37027604760085782803598745)
  ·
    refine ⟨27770703570064337102699059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37027604760085782803598745 27770703570064337102699059)
    ·
      refine ⟨41656055355096505654048589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27770703570064337102699059 41656055355096505654048589)
      ·
        refine ⟨15621020758161189620268221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41656055355096505654048589 15621020758161189620268221)
        ·
          refine ⟨5857882784310446107600583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15621020758161189620268221 5857882784310446107600583)
          ·
            refine ⟨8786824176465669161400875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857882784310446107600583 8786824176465669161400875)
            ·
              refine ⟨13180236264698503742101313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8786824176465669161400875 13180236264698503742101313)
              ·
                refine ⟨9885177198523877806575985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13180236264698503742101313 9885177198523877806575985)
                ·
                  refine ⟨7413882898892908354931989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885177198523877806575985 7413882898892908354931989)
                  ·
                    refine ⟨347525760885605079137437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7413882898892908354931989 347525760885605079137437)
                    ·
                      rfl

theorem cell23_2030412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_2030412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030412 prefixEnd_2030412 := by exact prefixLift 2030412
  have htrace : WordTrace (prefixWord ++ tailWord_2030412) baseStart_2030412 baseEnd_2030412 := by
    simpa [prefixWord, tailWord_2030412, baseEnd_2030412] using wordTrace_append hprefix tailTrace_2030412
  have hstable : (prefixWord ++ tailWord_2030412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030412).length < 2 ^ (prefixWord ++ tailWord_2030412).sum := by decide
  have hdescent : baseEnd_2030412 < baseStart_2030412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030413 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2030413 : Nat := 118140960795 + 2030413 * 2 ^ 59
def prefixEnd_2030413 : Nat := 4983230072969 + 3 ^ 40 * 2030413 * 2
def baseEnd_2030413 : Nat := 1042577796137469733499807

theorem tailTrace_2030413 : CollatzResearch.WordTrace tailWord_2030413 prefixEnd_2030413 1042577796137469733499807 := by
  unfold tailWord_2030413
  simp only [CollatzResearch.WordTrace]
  refine ⟨74055245993167942777983893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49370163995445295185322595 74055245993167942777983893)
  ·
    refine ⟨3471339655929747317717995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74055245993167942777983893 3471339655929747317717995)
    ·
      refine ⟨5207009483894620976576993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471339655929747317717995 5207009483894620976576993)
      ·
        refine ⟨3905257112920965732432745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5207009483894620976576993 3905257112920965732432745)
        ·
          refine ⟨2928942834690724299324559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905257112920965732432745 2928942834690724299324559)
          ·
            refine ⟨4393414252036086448986839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928942834690724299324559 4393414252036086448986839)
            ·
              refine ⟨6590121378054129673480259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393414252036086448986839 6590121378054129673480259)
              ·
                refine ⟨9885182067081194510220389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590121378054129673480259 9885182067081194510220389)
                ·
                  refine ⟨1853471637577723970666323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9885182067081194510220389 1853471637577723970666323)
                  ·
                    refine ⟨2780207456366585955999485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1853471637577723970666323 2780207456366585955999485)
                    ·
                      refine ⟨1042577796137469733499807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780207456366585955999485 1042577796137469733499807)
                      ·
                        rfl

theorem cell23_2030413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2030413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030413 prefixEnd_2030413 := by exact prefixLift 2030413
  have htrace : WordTrace (prefixWord ++ tailWord_2030413) baseStart_2030413 baseEnd_2030413 := by
    simpa [prefixWord, tailWord_2030413, baseEnd_2030413] using wordTrace_append hprefix tailTrace_2030413
  have hstable : (prefixWord ++ tailWord_2030413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030413).length < 2 ^ (prefixWord ++ tailWord_2030413).sum := by decide
  have hdescent : baseEnd_2030413 < baseStart_2030413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030432 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2030432 : Nat := 118140960795 + 2030432 * 2 ^ 59
def prefixEnd_2030432 : Nat := 4983230072969 + 3 ^ 40 * 2030432 * 2
def baseEnd_2030432 : Nat := 1042587552269905159162219

theorem tailTrace_2030432 : CollatzResearch.WordTrace tailWord_2030432 prefixEnd_2030432 1042587552269905159162219 := by
  unfold tailWord_2030432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37027969490049554511462775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49370625986732739348617033 37027969490049554511462775)
  ·
    refine ⟨55541954235074331767194163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37027969490049554511462775 55541954235074331767194163)
    ·
      refine ⟨83312931352611497650791245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55541954235074331767194163 83312931352611497650791245)
      ·
        refine ⟨31242349257229311619046717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83312931352611497650791245 31242349257229311619046717)
        ·
          refine ⟨11715880971460991857142519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31242349257229311619046717 11715880971460991857142519)
          ·
            refine ⟨17573821457191487785713779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715880971460991857142519 17573821457191487785713779)
            ·
              refine ⟨26360732185787231678570669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573821457191487785713779 26360732185787231678570669)
              ·
                refine ⟨9885274569670211879464001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26360732185787231678570669 9885274569670211879464001)
                ·
                  refine ⟨7413955927252658909598001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885274569670211879464001 7413955927252658909598001)
                  ·
                    refine ⟨5560466945439494182198501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7413955927252658909598001 5560466945439494182198501)
                    ·
                      refine ⟨1042587552269905159162219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5560466945439494182198501 1042587552269905159162219)
                      ·
                        rfl

theorem cell23_2030432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2030432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030432 prefixEnd_2030432 := by exact prefixLift 2030432
  have htrace : WordTrace (prefixWord ++ tailWord_2030432) baseStart_2030432 baseEnd_2030432 := by
    simpa [prefixWord, tailWord_2030432, baseEnd_2030432] using wordTrace_append hprefix tailTrace_2030432
  have hstable : (prefixWord ++ tailWord_2030432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030432).length < 2 ^ (prefixWord ++ tailWord_2030432).sum := by decide
  have hdescent : baseEnd_2030432 < baseStart_2030432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030436 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_2030436 : Nat := 118140960795 + 2030436 * 2 ^ 59
def prefixEnd_2030436 : Nat := 4983230072969 + 3 ^ 40 * 2030436 * 2
def baseEnd_2030436 : Nat := 1042589606192523143512201

theorem tailTrace_2030436 : CollatzResearch.WordTrace tailWord_2030436 prefixEnd_2030436 1042589606192523143512201 := by
  unfold tailWord_2030436
  simp only [CollatzResearch.WordTrace]
  refine ⟨37028042436042308853035581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49370723248056411804047441 37028042436042308853035581)
  ·
    refine ⟨13885515913515865819888343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37028042436042308853035581 13885515913515865819888343)
    ·
      refine ⟨20828273870273798729832515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13885515913515865819888343 20828273870273798729832515)
      ·
        refine ⟨31242410805410698094748773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20828273870273798729832515 31242410805410698094748773)
        ·
          refine ⟨5857952026014505892765395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31242410805410698094748773 5857952026014505892765395)
          ·
            refine ⟨8786928039021758839148093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857952026014505892765395 8786928039021758839148093)
            ·
              refine ⟨3295098014633159564680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8786928039021758839148093 3295098014633159564680535)
              ·
                refine ⟨4942647021949739347020803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295098014633159564680535 4942647021949739347020803)
                ·
                  refine ⟨7413970532924609020531205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942647021949739347020803 7413970532924609020531205)
                  ·
                    refine ⟨1390119474923364191349601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413970532924609020531205 1390119474923364191349601)
                    ·
                      refine ⟨1042589606192523143512201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390119474923364191349601 1042589606192523143512201)
                      ·
                        rfl

theorem cell23_2030436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_2030436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030436 prefixEnd_2030436 := by exact prefixLift 2030436
  have htrace : WordTrace (prefixWord ++ tailWord_2030436) baseStart_2030436 baseEnd_2030436 := by
    simpa [prefixWord, tailWord_2030436, baseEnd_2030436] using wordTrace_append hprefix tailTrace_2030436
  have hstable : (prefixWord ++ tailWord_2030436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030436).length < 2 ^ (prefixWord ++ tailWord_2030436).sum := by decide
  have hdescent : baseEnd_2030436 < baseStart_2030436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030459 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 5]
def baseStart_2030459 : Nat := 118140960795 + 2030459 * 2 ^ 59
def prefixEnd_2030459 : Nat := 4983230072969 + 3 ^ 40 * 2030459 * 2
def baseEnd_2030459 : Nat := 115844601805286283724955

theorem tailTrace_2030459 : CollatzResearch.WordTrace tailWord_2030459 prefixEnd_2030459 115844601805286283724955 := by
  unfold tailWord_2030459
  simp only [CollatzResearch.WordTrace]
  refine ⟨74056923751001292634158431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49371282500667528422772287 74056923751001292634158431)
  ·
    refine ⟨111085385626501938951237647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74056923751001292634158431 111085385626501938951237647)
    ·
      refine ⟨166628078439752908426856471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111085385626501938951237647 166628078439752908426856471)
      ·
        refine ⟨249942117659629362640284707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166628078439752908426856471 249942117659629362640284707)
        ·
          refine ⟨374913176489444043960427061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249942117659629362640284707 374913176489444043960427061)
          ·
            refine ⟨35148110295885379121290037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374913176489444043960427061 35148110295885379121290037)
            ·
              refine ⟨3295135340239254292620941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35148110295885379121290037 3295135340239254292620941)
              ·
                refine ⟨1235675752589720359732853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3295135340239254292620941 1235675752589720359732853)
                ·
                  refine ⟨115844601805286283724955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235675752589720359732853 115844601805286283724955)
                  ·
                    rfl

theorem cell23_2030459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 5].length) (baseStart_2030459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030459 prefixEnd_2030459 := by exact prefixLift 2030459
  have htrace : WordTrace (prefixWord ++ tailWord_2030459) baseStart_2030459 baseEnd_2030459 := by
    simpa [prefixWord, tailWord_2030459, baseEnd_2030459] using wordTrace_append hprefix tailTrace_2030459
  have hstable : (prefixWord ++ tailWord_2030459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030459).length < 2 ^ (prefixWord ++ tailWord_2030459).sum := by decide
  have hdescent : baseEnd_2030459 < baseStart_2030459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030516 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2030516 : Nat := 118140960795 + 2030516 * 2 ^ 59
def prefixEnd_2030516 : Nat := 4983230072969 + 3 ^ 40 * 2030516 * 2
def baseEnd_2030516 : Nat := 1042630684644882830511833

theorem tailTrace_2030516 : CollatzResearch.WordTrace tailWord_2030516 prefixEnd_2030516 1042630684644882830511833 := by
  unfold tailWord_2030516
  simp only [CollatzResearch.WordTrace]
  refine ⟨37029501355897395684491701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49372668474529860912655601 37029501355897395684491701)
  ·
    refine ⟨3471515752115380845421097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37029501355897395684491701 3471515752115380845421097)
    ·
      refine ⟨2603636814086535634065823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3471515752115380845421097 2603636814086535634065823)
      ·
        refine ⟨3905455221129803451098735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603636814086535634065823 3905455221129803451098735)
        ·
          refine ⟨5858182831694705176648103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905455221129803451098735 5858182831694705176648103)
          ·
            refine ⟨8787274247542057764972155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858182831694705176648103 8787274247542057764972155)
            ·
              refine ⟨13180911371313086647458233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787274247542057764972155 13180911371313086647458233)
              ·
                refine ⟨9885683528484814985593675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13180911371313086647458233 9885683528484814985593675)
                ·
                  refine ⟨14828525292727222478390513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9885683528484814985593675 14828525292727222478390513)
                  ·
                    refine ⟨11121393969545416858792885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14828525292727222478390513 11121393969545416858792885)
                    ·
                      refine ⟨1042630684644882830511833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11121393969545416858792885 1042630684644882830511833)
                      ·
                        rfl

theorem cell23_2030516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2030516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030516 prefixEnd_2030516 := by exact prefixLift 2030516
  have htrace : WordTrace (prefixWord ++ tailWord_2030516) baseStart_2030516 baseEnd_2030516 := by
    simpa [prefixWord, tailWord_2030516, baseEnd_2030516] using wordTrace_append hprefix tailTrace_2030516
  have hstable : (prefixWord ++ tailWord_2030516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030516).length < 2 ^ (prefixWord ++ tailWord_2030516).sum := by decide
  have hdescent : baseEnd_2030516 < baseStart_2030516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030522 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_2030522 : Nat := 118140960795 + 2030522 * 2 ^ 59
def prefixEnd_2030522 : Nat := 4983230072969 + 3 ^ 40 * 2030522 * 2
def baseEnd_2030522 : Nat := 1042633765528809807036805

theorem tailTrace_2030522 : CollatzResearch.WordTrace tailWord_2030522 prefixEnd_2030522 1042633765528809807036805 := by
  unfold tailWord_2030522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514805387443263598425455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49372814366515369595801213 18514805387443263598425455)
  ·
    refine ⟨27772208081164895397638183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18514805387443263598425455 27772208081164895397638183)
    ·
      refine ⟨41658312121747343096457275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772208081164895397638183 41658312121747343096457275)
      ·
        refine ⟨62487468182621014644685913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41658312121747343096457275 62487468182621014644685913)
        ·
          refine ⟨46865601136965760983514435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62487468182621014644685913 46865601136965760983514435)
          ·
            refine ⟨70298401705448641475271653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46865601136965760983514435 70298401705448641475271653)
            ·
              refine ⟨13180950319771620276613435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70298401705448641475271653 13180950319771620276613435)
              ·
                refine ⟨19771425479657430414920153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13180950319771620276613435 19771425479657430414920153)
                ·
                  refine ⟨14828569109743072811190115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19771425479657430414920153 14828569109743072811190115)
                  ·
                    refine ⟨22242853664614609216785173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14828569109743072811190115 22242853664614609216785173)
                    ·
                      refine ⟨1042633765528809807036805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22242853664614609216785173 1042633765528809807036805)
                      ·
                        rfl

theorem cell23_2030522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_2030522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030522 prefixEnd_2030522 := by exact prefixLift 2030522
  have htrace : WordTrace (prefixWord ++ tailWord_2030522) baseStart_2030522 baseEnd_2030522 := by
    simpa [prefixWord, tailWord_2030522, baseEnd_2030522] using wordTrace_append hprefix tailTrace_2030522
  have hstable : (prefixWord ++ tailWord_2030522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030522).length < 2 ^ (prefixWord ++ tailWord_2030522).sum := by decide
  have hdescent : baseEnd_2030522 < baseStart_2030522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030526 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_2030526 : Nat := 118140960795 + 2030526 * 2 ^ 59
def prefixEnd_2030526 : Nat := 4983230072969 + 3 ^ 40 * 2030526 * 2
def baseEnd_2030526 : Nat := 1042635819451427791386787

theorem tailTrace_2030526 : CollatzResearch.WordTrace tailWord_2030526 prefixEnd_2030526 1042635819451427791386787 := by
  unfold tailWord_2030526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257420930219820384605929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49372911627839042051231621 9257420930219820384605929)
  ·
    refine ⟨6943065697664865288454447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9257420930219820384605929 6943065697664865288454447)
    ·
      refine ⟨10414598546497297932681671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943065697664865288454447 10414598546497297932681671)
      ·
        refine ⟨15621897819745946899022507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10414598546497297932681671 15621897819745946899022507)
        ·
          refine ⟨23432846729618920348533761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15621897819745946899022507 23432846729618920348533761)
          ·
            refine ⟨17574635047214190261400321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23432846729618920348533761 17574635047214190261400321)
            ·
              refine ⟨13180976285410642696050241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17574635047214190261400321 13180976285410642696050241)
              ·
                refine ⟨9885732214057982022037681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13180976285410642696050241 9885732214057982022037681)
                ·
                  refine ⟨7414299160543486516528261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885732214057982022037681 7414299160543486516528261)
                  ·
                    refine ⟨1390181092601903721849049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414299160543486516528261 1390181092601903721849049)
                    ·
                      refine ⟨1042635819451427791386787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390181092601903721849049 1042635819451427791386787)
                      ·
                        rfl

theorem cell23_2030526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_2030526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030526 prefixEnd_2030526 := by exact prefixLift 2030526
  have htrace : WordTrace (prefixWord ++ tailWord_2030526) baseStart_2030526 baseEnd_2030526 := by
    simpa [prefixWord, tailWord_2030526, baseEnd_2030526] using wordTrace_append hprefix tailTrace_2030526
  have hstable : (prefixWord ++ tailWord_2030526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030526).length < 2 ^ (prefixWord ++ tailWord_2030526).sum := by decide
  have hdescent : baseEnd_2030526 < baseStart_2030526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030572 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2030572 : Nat := 118140960795 + 2030572 * 2 ^ 59
def prefixEnd_2030572 : Nat := 4983230072969 + 3 ^ 40 * 2030572 * 2
def baseEnd_2030572 : Nat := 1042659439561534611411575

theorem tailTrace_2030572 : CollatzResearch.WordTrace tailWord_2030572 prefixEnd_2030572 1042659439561534611411575 := by
  unfold tailWord_2030572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37030522599795956466510985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49374030133061275288681313 37030522599795956466510985)
  ·
    refine ⟨27772891949846967349883239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37030522599795956466510985 27772891949846967349883239)
    ·
      refine ⟨41659337924770451024824859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772891949846967349883239 41659337924770451024824859)
      ·
        refine ⟨62489006887155676537237289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41659337924770451024824859 62489006887155676537237289)
        ·
          refine ⟨46866755165366757402927967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62489006887155676537237289 46866755165366757402927967)
          ·
            refine ⟨70300132748050136104391951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46866755165366757402927967 70300132748050136104391951)
            ·
              refine ⟨105450199122075204156587927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70300132748050136104391951 105450199122075204156587927)
              ·
                refine ⟨158175298683112806234881891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105450199122075204156587927 158175298683112806234881891)
                ·
                  refine ⟨237262948024669209352322837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158175298683112806234881891 237262948024669209352322837)
                  ·
                    refine ⟨11121700688656369188390133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237262948024669209352322837 11121700688656369188390133)
                    ·
                      refine ⟨1042659439561534611411575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11121700688656369188390133 1042659439561534611411575)
                      ·
                        rfl

theorem cell23_2030572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2030572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030572 prefixEnd_2030572 := by exact prefixLift 2030572
  have htrace : WordTrace (prefixWord ++ tailWord_2030572) baseStart_2030572 baseEnd_2030572 := by
    simpa [prefixWord, tailWord_2030572, baseEnd_2030572] using wordTrace_append hprefix tailTrace_2030572
  have hstable : (prefixWord ++ tailWord_2030572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030572).length < 2 ^ (prefixWord ++ tailWord_2030572).sum := by decide
  have hdescent : baseEnd_2030572 < baseStart_2030572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030586 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_2030586 : Nat := 118140960795 + 2030586 * 2 ^ 59
def prefixEnd_2030586 : Nat := 4983230072969 + 3 ^ 40 * 2030586 * 2
def baseEnd_2030586 : Nat := 1042666628290697556636511

theorem tailTrace_2030586 : CollatzResearch.WordTrace tailWord_2030586 prefixEnd_2030586 1042666628290697556636511 := by
  unfold tailWord_2030586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515388955385298331007903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49374370547694128882687741 18515388955385298331007903)
  ·
    refine ⟨27773083433077947496511855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18515388955385298331007903 27773083433077947496511855)
    ·
      refine ⟨41659625149616921244767783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27773083433077947496511855 41659625149616921244767783)
      ·
        refine ⟨62489437724425381867151675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41659625149616921244767783 62489437724425381867151675)
        ·
          refine ⟨93734156586638072800727513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62489437724425381867151675 93734156586638072800727513)
          ·
            refine ⟨70300617439978554600545635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93734156586638072800727513 70300617439978554600545635)
            ·
              refine ⟨105450926159967831900818453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70300617439978554600545635 105450926159967831900818453)
              ·
                refine ⟨4943012163748492120350865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105450926159967831900818453 4943012163748492120350865)
                ·
                  refine ⟨3707259122811369090263149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4943012163748492120350865 3707259122811369090263149)
                  ·
                    refine ⟨1390222171054263408848681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3707259122811369090263149 1390222171054263408848681)
                    ·
                      refine ⟨1042666628290697556636511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390222171054263408848681 1042666628290697556636511)
                      ·
                        rfl

theorem cell23_2030586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_2030586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030586 prefixEnd_2030586 := by exact prefixLift 2030586
  have htrace : WordTrace (prefixWord ++ tailWord_2030586) baseStart_2030586 baseEnd_2030586 := by
    simpa [prefixWord, tailWord_2030586, baseEnd_2030586] using wordTrace_append hprefix tailTrace_2030586
  have hstable : (prefixWord ++ tailWord_2030586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030586).length < 2 ^ (prefixWord ++ tailWord_2030586).sum := by decide
  have hdescent : baseEnd_2030586 < baseStart_2030586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030593 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2030593 : Nat := 118140960795 + 2030593 * 2 ^ 59
def prefixEnd_2030593 : Nat := 4983230072969 + 3 ^ 40 * 2030593 * 2
def baseEnd_2030593 : Nat := 1042670222655279029248979

theorem tailTrace_2030593 : CollatzResearch.WordTrace tailWord_2030593 prefixEnd_2030593 1042670222655279029248979 := by
  unfold tailWord_2030593
  simp only [CollatzResearch.WordTrace]
  refine ⟨74061811132515833519536433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49374540755010555679690955 74061811132515833519536433)
  ·
    refine ⟨55546358349386875139652325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74061811132515833519536433 55546358349386875139652325)
    ·
      refine ⟨10414942190510039088684811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55546358349386875139652325 10414942190510039088684811)
      ·
        refine ⟨15622413285765058633027217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10414942190510039088684811 15622413285765058633027217)
        ·
          refine ⟨11716809964323793974770413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15622413285765058633027217 11716809964323793974770413)
          ·
            refine ⟨4393803736621422740538905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11716809964323793974770413 4393803736621422740538905)
            ·
              refine ⟨3295352802466067055404179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4393803736621422740538905 3295352802466067055404179)
              ·
                refine ⟨4943029203699100583106269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295352802466067055404179 4943029203699100583106269)
                ·
                  refine ⟨1853635951387162718664851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4943029203699100583106269 1853635951387162718664851)
                  ·
                    refine ⟨2780453927080744077997277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1853635951387162718664851 2780453927080744077997277)
                    ·
                      refine ⟨1042670222655279029248979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780453927080744077997277 1042670222655279029248979)
                      ·
                        rfl

theorem cell23_2030593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2030593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030593 prefixEnd_2030593 := by exact prefixLift 2030593
  have htrace : WordTrace (prefixWord ++ tailWord_2030593) baseStart_2030593 baseEnd_2030593 := by
    simpa [prefixWord, tailWord_2030593, baseEnd_2030593] using wordTrace_append hprefix tailTrace_2030593
  have hstable : (prefixWord ++ tailWord_2030593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030593).length < 2 ^ (prefixWord ++ tailWord_2030593).sum := by decide
  have hdescent : baseEnd_2030593 < baseStart_2030593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030616 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2030616 : Nat := 118140960795 + 2030616 * 2 ^ 59
def prefixEnd_2030616 : Nat := 4983230072969 + 3 ^ 40 * 2030616 * 2
def baseEnd_2030616 : Nat := 1042682032710332439261373

theorem tailTrace_2030616 : CollatzResearch.WordTrace tailWord_2030616 prefixEnd_2030616 1042682032710332439261373 := by
  unfold tailWord_2030616
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031325005716254223811851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49375100007621672298415801 37031325005716254223811851)
  ·
    refine ⟨55546987508574381335717777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37031325005716254223811851 55546987508574381335717777)
    ·
      refine ⟨41660240631430786001788333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55546987508574381335717777 41660240631430786001788333)
      ·
        refine ⟨15622590236786544750670625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41660240631430786001788333 15622590236786544750670625)
        ·
          refine ⟨11716942677589908563002969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15622590236786544750670625 11716942677589908563002969)
          ·
            refine ⟨8787707008192431422252227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11716942677589908563002969 8787707008192431422252227)
            ·
              refine ⟨13181560512288647133378341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787707008192431422252227 13181560512288647133378341)
              ·
                refine ⟨2471542596054121337508439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13181560512288647133378341 2471542596054121337508439)
                ·
                  refine ⟨3707313894081182006262659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471542596054121337508439 3707313894081182006262659)
                  ·
                    refine ⟨5560970841121773009393989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3707313894081182006262659 5560970841121773009393989)
                    ·
                      refine ⟨1042682032710332439261373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5560970841121773009393989 1042682032710332439261373)
                      ·
                        rfl

theorem cell23_2030616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2030616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030616 prefixEnd_2030616 := by exact prefixLift 2030616
  have htrace : WordTrace (prefixWord ++ tailWord_2030616) baseStart_2030616 baseEnd_2030616 := by
    simpa [prefixWord, tailWord_2030616, baseEnd_2030616] using wordTrace_append hprefix tailTrace_2030616
  have hstable : (prefixWord ++ tailWord_2030616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030616).length < 2 ^ (prefixWord ++ tailWord_2030616).sum := by decide
  have hdescent : baseEnd_2030616 < baseStart_2030616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030619 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3]
def baseStart_2030619 : Nat := 118140960795 + 2030619 * 2 ^ 59
def prefixEnd_2030619 : Nat := 4983230072969 + 3 ^ 40 * 2030619 * 2
def baseEnd_2030619 : Nat := 1042683573152295927523859

theorem tailTrace_2030619 : CollatzResearch.WordTrace tailWord_2030619 prefixEnd_2030619 1042683573152295927523859 := by
  unfold tailWord_2030619
  simp only [CollatzResearch.WordTrace]
  refine ⟨74062759430421639959982911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49375172953614426639988607 74062759430421639959982911)
  ·
    refine ⟨111094139145632459939974367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74062759430421639959982911 111094139145632459939974367)
    ·
      refine ⟨166641208718448689909961551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111094139145632459939974367 166641208718448689909961551)
      ·
        refine ⟨249961813077673034864942327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166641208718448689909961551 249961813077673034864942327)
        ·
          refine ⟨374942719616509552297413491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249961813077673034864942327 374942719616509552297413491)
          ·
            refine ⟨562414079424764328446120237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374942719616509552297413491 562414079424764328446120237)
            ·
              refine ⟨210905279784286623167295089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562414079424764328446120237 210905279784286623167295089)
              ·
                refine ⟨158178959838214967375471317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210905279784286623167295089 158178959838214967375471317)
                ·
                  refine ⟨3707319371208163297862609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 158178959838214967375471317 3707319371208163297862609)
                  ·
                    refine ⟨2780489528406122473396957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3707319371208163297862609 2780489528406122473396957)
                    ·
                      refine ⟨1042683573152295927523859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780489528406122473396957 1042683573152295927523859)
                      ·
                        rfl

theorem cell23_2030619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3].length) (baseStart_2030619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030619 prefixEnd_2030619 := by exact prefixLift 2030619
  have htrace : WordTrace (prefixWord ++ tailWord_2030619) baseStart_2030619 baseEnd_2030619 := by
    simpa [prefixWord, tailWord_2030619, baseEnd_2030619] using wordTrace_append hprefix tailTrace_2030619
  have hstable : (prefixWord ++ tailWord_2030619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030619).length < 2 ^ (prefixWord ++ tailWord_2030619).sum := by decide
  have hdescent : baseEnd_2030619 < baseStart_2030619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030626 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2030626 : Nat := 118140960795 + 2030626 * 2 ^ 59
def prefixEnd_2030626 : Nat := 4983230072969 + 3 ^ 40 * 2030626 * 2
def baseEnd_2030626 : Nat := 347562389172292466712109

theorem tailTrace_2030626 : CollatzResearch.WordTrace tailWord_2030626 prefixEnd_2030626 347562389172292466712109 := by
  unfold tailWord_2030626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515753685349070038871933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49375343160930853436991821 18515753685349070038871933)
  ·
    refine ⟨6943407632005901264576975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18515753685349070038871933 6943407632005901264576975)
    ·
      refine ⟨10415111448008851896865463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943407632005901264576975 10415111448008851896865463)
      ·
        refine ⟨15622667172013277845298195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415111448008851896865463 15622667172013277845298195)
        ·
          refine ⟨23434000758019916767947293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15622667172013277845298195 23434000758019916767947293)
          ·
            refine ⟨8787750284257468787980235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23434000758019916767947293 8787750284257468787980235)
            ·
              refine ⟨13181625426386203181970353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787750284257468787980235 13181625426386203181970353)
              ·
                refine ⟨9886219069789652386477765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181625426386203181970353 9886219069789652386477765)
                ·
                  refine ⟨1853666075585559822464581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9886219069789652386477765 1853666075585559822464581)
                  ·
                    refine ⟨347562389172292466712109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1853666075585559822464581 347562389172292466712109)
                    ·
                      rfl

theorem cell23_2030626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2030626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030626 prefixEnd_2030626 := by exact prefixLift 2030626
  have htrace : WordTrace (prefixWord ++ tailWord_2030626) baseStart_2030626 baseEnd_2030626 := by
    simpa [prefixWord, tailWord_2030626, baseEnd_2030626] using wordTrace_append hprefix tailTrace_2030626
  have hstable : (prefixWord ++ tailWord_2030626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030626).length < 2 ^ (prefixWord ++ tailWord_2030626).sum := by decide
  have hdescent : baseEnd_2030626 < baseStart_2030626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030629 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_2030629 : Nat := 118140960795 + 2030629 * 2 ^ 59
def prefixEnd_2030629 : Nat := 4983230072969 + 3 ^ 40 * 2030629 * 2
def baseEnd_2030629 : Nat := 1042688707958840888398813

theorem tailTrace_2030629 : CollatzResearch.WordTrace tailWord_2030629 prefixEnd_2030629 1042688707958840888398813 := by
  unfold tailWord_2030629
  simp only [CollatzResearch.WordTrace]
  refine ⟨74063124160385411667846941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49375416106923607778564627 74063124160385411667846941)
  ·
    refine ⟨27773671560144529375442603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74063124160385411667846941 27773671560144529375442603)
    ·
      refine ⟨41660507340216794063163905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27773671560144529375442603 41660507340216794063163905)
      ·
        refine ⟨31245380505162595547372929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41660507340216794063163905 31245380505162595547372929)
        ·
          refine ⟨23434035378871946660529697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31245380505162595547372929 23434035378871946660529697)
          ·
            refine ⟨17575526534153959995397273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23434035378871946660529697 17575526534153959995397273)
            ·
              refine ⟨13181644900615469996547955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17575526534153959995397273 13181644900615469996547955)
              ·
                refine ⟨19772467350923204994821933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181644900615469996547955 19772467350923204994821933)
                ·
                  refine ⟨7414675256596201873058225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19772467350923204994821933 7414675256596201873058225)
                  ·
                    refine ⟨5561006442447151404793669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7414675256596201873058225 5561006442447151404793669)
                    ·
                      refine ⟨1042688707958840888398813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5561006442447151404793669 1042688707958840888398813)
                      ·
                        rfl

theorem cell23_2030629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_2030629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030629 prefixEnd_2030629 := by exact prefixLift 2030629
  have htrace : WordTrace (prefixWord ++ tailWord_2030629) baseStart_2030629 baseEnd_2030629 := by
    simpa [prefixWord, tailWord_2030629, baseEnd_2030629] using wordTrace_append hprefix tailTrace_2030629
  have hstable : (prefixWord ++ tailWord_2030629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030629).length < 2 ^ (prefixWord ++ tailWord_2030629).sum := by decide
  have hdescent : baseEnd_2030629 < baseStart_2030629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030636 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_2030636 : Nat := 118140960795 + 2030636 * 2 ^ 59
def prefixEnd_2030636 : Nat := 4983230072969 + 3 ^ 40 * 2030636 * 2
def baseEnd_2030636 : Nat := 1042692302323422361011281

theorem tailTrace_2030636 : CollatzResearch.WordTrace tailWord_2030636 prefixEnd_2030636 1042692302323422361011281 := by
  unfold tailWord_2030636
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031689735680025931675881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49375586314240034575567841 37031689735680025931675881)
  ·
    refine ⟨27773767301760019448756911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37031689735680025931675881 27773767301760019448756911)
    ·
      refine ⟨41660650952640029173135367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27773767301760019448756911 41660650952640029173135367)
      ·
        refine ⟨62490976428960043759703051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41660650952640029173135367 62490976428960043759703051)
        ·
          refine ⟨93736464643440065639554577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62490976428960043759703051 93736464643440065639554577)
          ·
            refine ⟨70302348482580049229665933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93736464643440065639554577 70302348482580049229665933)
            ·
              refine ⟨26363380680967518461124725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70302348482580049229665933 26363380680967518461124725)
              ·
                refine ⟨2471566938840704855730443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26363380680967518461124725 2471566938840704855730443)
                ·
                  refine ⟨3707350408261057283595665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471566938840704855730443 3707350408261057283595665)
                  ·
                    refine ⟨2780512806195792962696749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3707350408261057283595665 2780512806195792962696749)
                    ·
                      refine ⟨1042692302323422361011281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780512806195792962696749 1042692302323422361011281)
                      ·
                        rfl

theorem cell23_2030636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_2030636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030636 prefixEnd_2030636 := by exact prefixLift 2030636
  have htrace : WordTrace (prefixWord ++ tailWord_2030636) baseStart_2030636 baseEnd_2030636 := by
    simpa [prefixWord, tailWord_2030636, baseEnd_2030636] using wordTrace_append hprefix tailTrace_2030636
  have hstable : (prefixWord ++ tailWord_2030636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030636).length < 2 ^ (prefixWord ++ tailWord_2030636).sum := by decide
  have hdescent : baseEnd_2030636 < baseStart_2030636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030644 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2030644 : Nat := 118140960795 + 2030644 * 2 ^ 59
def prefixEnd_2030644 : Nat := 4983230072969 + 3 ^ 40 * 2030644 * 2
def baseEnd_2030644 : Nat := 1042696410168658329711245

theorem tailTrace_2030644 : CollatzResearch.WordTrace tailWord_2030644 prefixEnd_2030644 1042696410168658329711245 := by
  unfold tailWord_2030644
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031835627665534614821493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49375780836887379486428657 37031835627665534614821493)
  ·
    refine ⟨3471734590093643870139515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37031835627665534614821493 3471734590093643870139515)
    ·
      refine ⟨5207601885140465805209273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471734590093643870139515 5207601885140465805209273)
      ·
        refine ⟨3905701413855349353906955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5207601885140465805209273 3905701413855349353906955)
        ·
          refine ⟨5858552120783024030860433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905701413855349353906955 5858552120783024030860433)
          ·
            refine ⟨4393914090587268023145325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5858552120783024030860433 4393914090587268023145325)
            ·
              refine ⟨1647717783970225508679497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4393914090587268023145325 1647717783970225508679497)
              ·
                refine ⟨1235788337977669131509623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647717783970225508679497 1235788337977669131509623)
                ·
                  refine ⟨1853682506966503697264435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235788337977669131509623 1853682506966503697264435)
                  ·
                    refine ⟨2780523760449755545896653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1853682506966503697264435 2780523760449755545896653)
                    ·
                      refine ⟨1042696410168658329711245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780523760449755545896653 1042696410168658329711245)
                      ·
                        rfl

theorem cell23_2030644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2030644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030644 prefixEnd_2030644 := by exact prefixLift 2030644
  have htrace : WordTrace (prefixWord ++ tailWord_2030644) baseStart_2030644 baseEnd_2030644 := by
    simpa [prefixWord, tailWord_2030644, baseEnd_2030644] using wordTrace_append hprefix tailTrace_2030644
  have hstable : (prefixWord ++ tailWord_2030644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030644).length < 2 ^ (prefixWord ++ tailWord_2030644).sum := by decide
  have hdescent : baseEnd_2030644 < baseStart_2030644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030646 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2030646 : Nat := 118140960795 + 2030646 * 2 ^ 59
def prefixEnd_2030646 : Nat := 4983230072969 + 3 ^ 40 * 2030646 * 2
def baseEnd_2030646 : Nat := 1042697437129967321886235

theorem tailTrace_2030646 : CollatzResearch.WordTrace tailWord_2030646 prefixEnd_2030646 1042697437129967321886235 := by
  unfold tailWord_2030646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628984012582738973200987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49375829467549215714143861 4628984012582738973200987)
  ·
    refine ⟨6943476018874108459801481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628984012582738973200987 6943476018874108459801481)
    ·
      refine ⟨5207607014155581344851111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6943476018874108459801481 5207607014155581344851111)
      ·
        refine ⟨7811410521233372017276667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5207607014155581344851111 7811410521233372017276667)
        ·
          refine ⟨11717115781850058025915001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811410521233372017276667 11717115781850058025915001)
          ·
            refine ⟨8787836836387543519436251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11717115781850058025915001 8787836836387543519436251)
            ·
              refine ⟨13181755254581315279154377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787836836387543519436251 13181755254581315279154377)
              ·
                refine ⟨9886316440935986459365783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181755254581315279154377 9886316440935986459365783)
                ·
                  refine ⟨14829474661403979689048675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9886316440935986459365783 14829474661403979689048675)
                  ·
                    refine ⟨22244211992105969533573013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14829474661403979689048675 22244211992105969533573013)
                    ·
                      refine ⟨1042697437129967321886235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22244211992105969533573013 1042697437129967321886235)
                      ·
                        rfl

theorem cell23_2030646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2030646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030646 prefixEnd_2030646 := by exact prefixLift 2030646
  have htrace : WordTrace (prefixWord ++ tailWord_2030646) baseStart_2030646 baseEnd_2030646 := by
    simpa [prefixWord, tailWord_2030646, baseEnd_2030646] using wordTrace_append hprefix tailTrace_2030646
  have hstable : (prefixWord ++ tailWord_2030646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030646).length < 2 ^ (prefixWord ++ tailWord_2030646).sum := by decide
  have hdescent : baseEnd_2030646 < baseStart_2030646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030650 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2]
def baseStart_2030650 : Nat := 118140960795 + 2030650 * 2 ^ 59
def prefixEnd_2030650 : Nat := 4983230072969 + 3 ^ 40 * 2030650 * 2
def baseEnd_2030650 : Nat := 1042699491052585306236217

theorem tailTrace_2030650 : CollatzResearch.WordTrace tailWord_2030650 prefixEnd_2030650 1042699491052585306236217 := by
  unfold tailWord_2030650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515972523327333063590351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49375926728872888169574269 18515972523327333063590351)
  ·
    refine ⟨27773958784990999595385527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18515972523327333063590351 27773958784990999595385527)
    ·
      refine ⟨41660938177486499393078291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27773958784990999595385527 41660938177486499393078291)
      ·
        refine ⟨62491407266229749089617437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41660938177486499393078291 62491407266229749089617437)
        ·
          refine ⟨23434277724836155908606539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62491407266229749089617437 23434277724836155908606539)
          ·
            refine ⟨35151416587254233862909809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23434277724836155908606539 35151416587254233862909809)
            ·
              refine ⟨26363562440440675397182357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35151416587254233862909809 26363562440440675397182357)
              ·
                refine ⟨1235791989395656659242923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26363562440440675397182357 1235791989395656659242923)
                ·
                  refine ⟨1853687984093484988864385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235791989395656659242923 1853687984093484988864385)
                  ·
                    refine ⟨1390265988070113741648289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853687984093484988864385 1390265988070113741648289)
                    ·
                      refine ⟨1042699491052585306236217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390265988070113741648289 1042699491052585306236217)
                      ·
                        rfl

theorem cell23_2030650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_2030650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030650 prefixEnd_2030650 := by exact prefixLift 2030650
  have htrace : WordTrace (prefixWord ++ tailWord_2030650) baseStart_2030650 baseEnd_2030650 := by
    simpa [prefixWord, tailWord_2030650, baseEnd_2030650] using wordTrace_append hprefix tailTrace_2030650
  have hstable : (prefixWord ++ tailWord_2030650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030650).length < 2 ^ (prefixWord ++ tailWord_2030650).sum := by decide
  have hdescent : baseEnd_2030650 < baseStart_2030650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030723 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 1, 4, 2]
def baseStart_2030723 : Nat := 118140960795 + 2030723 * 2 ^ 59
def prefixEnd_2030723 : Nat := 4983230072969 + 3 ^ 40 * 2030723 * 2
def baseEnd_2030723 : Nat := 1042736975140363520623381

theorem tailTrace_2030723 : CollatzResearch.WordTrace tailWord_2030723 prefixEnd_2030723 1042736975140363520623381 := by
  unfold tailWord_2030723
  simp only [CollatzResearch.WordTrace]
  refine ⟨74066552622044865721768823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49377701748029910481179215 74066552622044865721768823)
  ·
    refine ⟨111099828933067298582653235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74066552622044865721768823 111099828933067298582653235)
    ·
      refine ⟨166649743399600947873979853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111099828933067298582653235 166649743399600947873979853)
      ·
        refine ⟨62493653774850355452742445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166649743399600947873979853 62493653774850355452742445)
        ·
          refine ⟨23435120165568883294778417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62493653774850355452742445 23435120165568883294778417)
          ·
            refine ⟨17576340124176662471083813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23435120165568883294778417 17576340124176662471083813)
            ·
              refine ⟨3295563773283124213328215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17576340124176662471083813 3295563773283124213328215)
              ·
                refine ⟨4943345659924686319992323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295563773283124213328215 4943345659924686319992323)
                ·
                  refine ⟨7415018489887029479988485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943345659924686319992323 7415018489887029479988485)
                  ·
                    refine ⟨1390315966853818027497841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415018489887029479988485 1390315966853818027497841)
                    ·
                      refine ⟨1042736975140363520623381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390315966853818027497841 1042736975140363520623381)
                      ·
                        rfl

theorem cell23_2030723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_2030723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030723 prefixEnd_2030723 := by exact prefixLift 2030723
  have htrace : WordTrace (prefixWord ++ tailWord_2030723) baseStart_2030723 baseEnd_2030723 := by
    simpa [prefixWord, tailWord_2030723, baseEnd_2030723] using wordTrace_append hprefix tailTrace_2030723
  have hstable : (prefixWord ++ tailWord_2030723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030723).length < 2 ^ (prefixWord ++ tailWord_2030723).sum := by decide
  have hdescent : baseEnd_2030723 < baseStart_2030723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030729 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 9]
def baseStart_2030729 : Nat := 118140960795 + 2030729 * 2 ^ 59
def prefixEnd_2030729 : Nat := 4983230072969 + 3 ^ 40 * 2030729 * 2
def baseEnd_2030729 : Nat := 115860006224921166349817

theorem tailTrace_2030729 : CollatzResearch.WordTrace tailWord_2030729 prefixEnd_2030729 115860006224921166349817 := by
  unfold tailWord_2030729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74066771460023128746487241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49377847640015419164324827 74066771460023128746487241)
  ·
    refine ⟨55550078595017346559865431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74066771460023128746487241 55550078595017346559865431)
    ·
      refine ⟨83325117892526019839798147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55550078595017346559865431 83325117892526019839798147)
      ·
        refine ⟨124987676838789029759697221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83325117892526019839798147 124987676838789029759697221)
        ·
          refine ⟨23435189407272943079943229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124987676838789029759697221 23435189407272943079943229)
          ·
            refine ⟨8788196027727353654978711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23435189407272943079943229 8788196027727353654978711)
            ·
              refine ⟨13182294041591030482468067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8788196027727353654978711 13182294041591030482468067)
              ·
                refine ⟨19773441062386545723702101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13182294041591030482468067 19773441062386545723702101)
                ·
                  refine ⟨115860006224921166349817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19773441062386545723702101 115860006224921166349817)
                  ·
                    rfl

theorem cell23_2030729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_2030729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030729 prefixEnd_2030729 := by exact prefixLift 2030729
  have htrace : WordTrace (prefixWord ++ tailWord_2030729) baseStart_2030729 baseEnd_2030729 := by
    simpa [prefixWord, tailWord_2030729, baseEnd_2030729] using wordTrace_append hprefix tailTrace_2030729
  have hstable : (prefixWord ++ tailWord_2030729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030729).length < 2 ^ (prefixWord ++ tailWord_2030729).sum := by decide
  have hdescent : baseEnd_2030729 < baseStart_2030729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030757 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 2, 2, 2]
def baseStart_2030757 : Nat := 118140960795 + 2030757 * 2 ^ 59
def prefixEnd_2030757 : Nat := 4983230072969 + 3 ^ 40 * 2030757 * 2
def baseEnd_2030757 : Nat := 1042754433482616387598225

theorem tailTrace_2030757 : CollatzResearch.WordTrace tailWord_2030757 prefixEnd_2030757 1042754433482616387598225 := by
  unfold tailWord_2030757
  simp only [CollatzResearch.WordTrace]
  refine ⟨74067792703921689528506525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49378528469281126352337683 74067792703921689528506525)
  ·
    refine ⟨27775422263970633573189947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74067792703921689528506525 27775422263970633573189947)
    ·
      refine ⟨41663133395955950359784921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775422263970633573189947 41663133395955950359784921)
      ·
        refine ⟨31247350046966962769838691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41663133395955950359784921 31247350046966962769838691)
        ·
          refine ⟨46871025070450444154758037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31247350046966962769838691 46871025070450444154758037)
          ·
            refine ⟨2197079300177364569754283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46871025070450444154758037 2197079300177364569754283)
            ·
              refine ⟨3295618950266046854631425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197079300177364569754283 3295618950266046854631425)
              ·
                refine ⟨2471714212699535140973569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3295618950266046854631425 2471714212699535140973569)
                ·
                  refine ⟨1853785659524651355730177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2471714212699535140973569 1853785659524651355730177)
                  ·
                    refine ⟨1390339244643488516797633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853785659524651355730177 1390339244643488516797633)
                    ·
                      refine ⟨1042754433482616387598225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390339244643488516797633 1042754433482616387598225)
                      ·
                        rfl

theorem cell23_2030757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_2030757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030757 prefixEnd_2030757 := by exact prefixLift 2030757
  have htrace : WordTrace (prefixWord ++ tailWord_2030757) baseStart_2030757 baseEnd_2030757 := by
    simpa [prefixWord, tailWord_2030757, baseEnd_2030757] using wordTrace_append hprefix tailTrace_2030757
  have hstable : (prefixWord ++ tailWord_2030757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030757).length < 2 ^ (prefixWord ++ tailWord_2030757).sum := by decide
  have hdescent : baseEnd_2030757 < baseStart_2030757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030789 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_2030789 : Nat := 118140960795 + 2030789 * 2 ^ 59
def prefixEnd_2030789 : Nat := 4983230072969 + 3 ^ 40 * 2030789 * 2
def baseEnd_2030789 : Nat := 347590288287853420799359

theorem tailTrace_2030789 : CollatzResearch.WordTrace tailWord_2030789 prefixEnd_2030789 347590288287853420799359 := by
  unfold tailWord_2030789
  simp only [CollatzResearch.WordTrace]
  refine ⟨74068959839805758993671421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49379306559870505995780947 74068959839805758993671421)
  ·
    refine ⟨27775859939927159622626783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74068959839805758993671421 27775859939927159622626783)
    ·
      refine ⟨41663789909890739433940175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775859939927159622626783 41663789909890739433940175)
      ·
        refine ⟨62495684864836109150910263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663789909890739433940175 62495684864836109150910263)
        ·
          refine ⟨93743527297254163726365395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62495684864836109150910263 93743527297254163726365395)
          ·
            refine ⟨140615290945881245589548093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93743527297254163726365395 140615290945881245589548093)
            ·
              refine ⟨52730734104705467096080535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140615290945881245589548093 52730734104705467096080535)
              ·
                refine ⟨79096101157058200644120803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52730734104705467096080535 79096101157058200644120803)
                ·
                  refine ⟨118644151735587300966181205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79096101157058200644120803 118644151735587300966181205)
                  ·
                    refine ⟨347590288287853420799359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 118644151735587300966181205 347590288287853420799359)
                    ·
                      rfl

theorem cell23_2030789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_2030789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030789 prefixEnd_2030789 := by exact prefixLift 2030789
  have htrace : WordTrace (prefixWord ++ tailWord_2030789) baseStart_2030789 baseEnd_2030789 := by
    simpa [prefixWord, tailWord_2030789, baseEnd_2030789] using wordTrace_append hprefix tailTrace_2030789
  have hstable : (prefixWord ++ tailWord_2030789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030789).length < 2 ^ (prefixWord ++ tailWord_2030789).sum := by decide
  have hdescent : baseEnd_2030789 < baseStart_2030789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030874 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_2030874 : Nat := 118140960795 + 2030874 * 2 ^ 59
def prefixEnd_2030874 : Nat := 4983230072969 + 3 ^ 40 * 2030874 * 2
def baseEnd_2030874 : Nat := 347604836906397476611729

theorem tailTrace_2030874 : CollatzResearch.WordTrace tailWord_2030874 prefixEnd_2030874 347604836906397476611729 := by
  unfold tailWord_2030874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518015011124454627628919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49381373362998545673677117 18518015011124454627628919)
  ·
    refine ⟨27777022516686681941443379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18518015011124454627628919 27777022516686681941443379)
    ·
      refine ⟨41665533775030022912165069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27777022516686681941443379 41665533775030022912165069)
      ·
        refine ⟨15624575165636258592061901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41665533775030022912165069 15624575165636258592061901)
        ·
          refine ⟨5859215687113596972023213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15624575165636258592061901 5859215687113596972023213)
          ·
            refine ⟨2197205882667598864508705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5859215687113596972023213 2197205882667598864508705)
            ·
              refine ⟨1647904412000699148381529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197205882667598864508705 1647904412000699148381529)
              ·
                refine ⟨1235928309000524361286147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647904412000699148381529 1235928309000524361286147)
                ·
                  refine ⟨1853892463500786541929221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1235928309000524361286147 1853892463500786541929221)
                  ·
                    refine ⟨347604836906397476611729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1853892463500786541929221 347604836906397476611729)
                    ·
                      rfl

theorem cell23_2030874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_2030874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030874 prefixEnd_2030874 := by exact prefixLift 2030874
  have htrace : WordTrace (prefixWord ++ tailWord_2030874) baseStart_2030874 baseEnd_2030874 := by
    simpa [prefixWord, tailWord_2030874, baseEnd_2030874] using wordTrace_append hprefix tailTrace_2030874
  have hstable : (prefixWord ++ tailWord_2030874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030874).length < 2 ^ (prefixWord ++ tailWord_2030874).sum := by decide
  have hdescent : baseEnd_2030874 < baseStart_2030874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030900 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2030900 : Nat := 118140960795 + 2030900 * 2 ^ 59
def prefixEnd_2030900 : Nat := 4983230072969 + 3 ^ 40 * 2030900 * 2
def baseEnd_2030900 : Nat := 347609287072069776036689

theorem tailTrace_2030900 : CollatzResearch.WordTrace tailWord_2030900 prefixEnd_2030900 347609287072069776036689 := by
  unfold tailWord_2030900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37036504171201812475481077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49382005561602416633974769 37036504171201812475481077)
  ·
    refine ⟨3472172266050169919576351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37036504171201812475481077 3472172266050169919576351)
    ·
      refine ⟨5208258399075254879364527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472172266050169919576351 5208258399075254879364527)
      ·
        refine ⟨7812387598612882319046791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208258399075254879364527 7812387598612882319046791)
        ·
          refine ⟨11718581397919323478570187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812387598612882319046791 11718581397919323478570187)
          ·
            refine ⟨17577872096878985217855281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11718581397919323478570187 17577872096878985217855281)
            ·
              refine ⟨13183404072659238913391461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17577872096878985217855281 13183404072659238913391461)
              ·
                refine ⟨2471888263623607296260899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13183404072659238913391461 2471888263623607296260899)
                ·
                  refine ⟨3707832395435410944391349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471888263623607296260899 3707832395435410944391349)
                  ·
                    refine ⟨347609287072069776036689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3707832395435410944391349 347609287072069776036689)
                    ·
                      rfl

theorem cell23_2030900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2030900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030900 prefixEnd_2030900 := by exact prefixLift 2030900
  have htrace : WordTrace (prefixWord ++ tailWord_2030900) baseStart_2030900 baseEnd_2030900 := by
    simpa [prefixWord, tailWord_2030900, baseEnd_2030900] using wordTrace_append hprefix tailTrace_2030900
  have hstable : (prefixWord ++ tailWord_2030900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030900).length < 2 ^ (prefixWord ++ tailWord_2030900).sum := by decide
  have hdescent : baseEnd_2030900 < baseStart_2030900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030920 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_2030920 : Nat := 118140960795 + 2030920 * 2 ^ 59
def prefixEnd_2030920 : Nat := 4983230072969 + 3 ^ 40 * 2030920 * 2
def baseEnd_2030920 : Nat := 1042838130829299249859975

theorem tailTrace_2030920 : CollatzResearch.WordTrace tailWord_2030920 prefixEnd_2030920 1042838130829299249859975 := by
  unfold tailWord_2030920
  simp only [CollatzResearch.WordTrace]
  refine ⟨37036868901165584183345107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49382491868220778911126809 37036868901165584183345107)
  ·
    refine ⟨55555303351748376275017661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37036868901165584183345107 55555303351748376275017661)
    ·
      refine ⟨20833238756905641103131623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55555303351748376275017661 20833238756905641103131623)
      ·
        refine ⟨31249858135358461654697435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833238756905641103131623 31249858135358461654697435)
        ·
          refine ⟨46874787203037692482046153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31249858135358461654697435 46874787203037692482046153)
          ·
            refine ⟨35156090402278269361534615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46874787203037692482046153 35156090402278269361534615)
            ·
              refine ⟨52734135603417404042301923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35156090402278269361534615 52734135603417404042301923)
              ·
                refine ⟨79101203405126106063452885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52734135603417404042301923 79101203405126106063452885)
                ·
                  refine ⟨1853934454807643110862177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79101203405126106063452885 1853934454807643110862177)
                  ·
                    refine ⟨1390450841105732333146633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1853934454807643110862177 1390450841105732333146633)
                    ·
                      refine ⟨1042838130829299249859975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390450841105732333146633 1042838130829299249859975)
                      ·
                        rfl

theorem cell23_2030920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_2030920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030920 prefixEnd_2030920 := by exact prefixLift 2030920
  have htrace : WordTrace (prefixWord ++ tailWord_2030920) baseStart_2030920 baseEnd_2030920 := by
    simpa [prefixWord, tailWord_2030920, baseEnd_2030920] using wordTrace_append hprefix tailTrace_2030920
  have hstable : (prefixWord ++ tailWord_2030920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030920).length < 2 ^ (prefixWord ++ tailWord_2030920).sum := by decide
  have hdescent : baseEnd_2030920 < baseStart_2030920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030926 : List Nat := [4, 1, 1, 1, 1, 1, 14]
def baseStart_2030926 : Nat := 118140960795 + 2030926 * 2 ^ 59
def prefixEnd_2030926 : Nat := 4983230072969 + 3 ^ 40 * 2030926 * 2
def baseEnd_2030926 : Nat := 12874582860657113905987

theorem tailTrace_2030926 : CollatzResearch.WordTrace tailWord_2030926 prefixEnd_2030926 12874582860657113905987 := by
  unfold tailWord_2030926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259244580038678923926079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49382637760206287594272421 9259244580038678923926079)
  ·
    refine ⟨13888866870058018385889119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9259244580038678923926079 13888866870058018385889119)
    ·
      refine ⟨20833300305087027578833679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13888866870058018385889119 20833300305087027578833679)
      ·
        refine ⟨31249950457630541368250519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833300305087027578833679 31249950457630541368250519)
        ·
          refine ⟨46874925686445812052375779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31249950457630541368250519 46874925686445812052375779)
          ·
            refine ⟨70312388529668718078563669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46874925686445812052375779 70312388529668718078563669)
            ·
              refine ⟨12874582860657113905987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 70312388529668718078563669 12874582860657113905987)
              ·
                rfl

theorem cell23_2030926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 14].length) (baseStart_2030926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030926 prefixEnd_2030926 := by exact prefixLift 2030926
  have htrace : WordTrace (prefixWord ++ tailWord_2030926) baseStart_2030926 baseEnd_2030926 := by
    simpa [prefixWord, tailWord_2030926, baseEnd_2030926] using wordTrace_append hprefix tailTrace_2030926
  have hstable : (prefixWord ++ tailWord_2030926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030926).length < 2 ^ (prefixWord ++ tailWord_2030926).sum := by decide
  have hdescent : baseEnd_2030926 < baseStart_2030926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030947 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 2, 4]
def baseStart_2030947 : Nat := 118140960795 + 2030947 * 2 ^ 59
def prefixEnd_2030947 : Nat := 4983230072969 + 3 ^ 40 * 2030947 * 2
def baseEnd_2030947 : Nat := 347617331602323548074117

theorem tailTrace_2030947 : CollatzResearch.WordTrace tailWord_2030947 prefixEnd_2030947 347617331602323548074117 := by
  unfold tailWord_2030947
  simp only [CollatzResearch.WordTrace]
  refine ⟨74074722573233351977923095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49383148382155567985282063 74074722573233351977923095)
  ·
    refine ⟨111112083859850027966884643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74074722573233351977923095 111112083859850027966884643)
    ·
      refine ⟨166668125789775041950326965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111112083859850027966884643 166668125789775041950326965)
      ·
        refine ⟨15625136792791410182843153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166668125789775041950326965 15625136792791410182843153)
        ·
          refine ⟨11718852594593557637132365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15625136792791410182843153 11718852594593557637132365)
          ·
            refine ⟨4394569722972584113924637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11718852594593557637132365 4394569722972584113924637)
            ·
              refine ⟨1647963646114719042721739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4394569722972584113924637 1647963646114719042721739)
              ·
                refine ⟨2471945469172078564082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647963646114719042721739 2471945469172078564082609)
                ·
                  refine ⟨1853959101879058923061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2471945469172078564082609 1853959101879058923061957)
                  ·
                    refine ⟨347617331602323548074117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1853959101879058923061957 347617331602323548074117)
                    ·
                      rfl

theorem cell23_2030947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 4].length) (baseStart_2030947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030947 prefixEnd_2030947 := by exact prefixLift 2030947
  have htrace : WordTrace (prefixWord ++ tailWord_2030947) baseStart_2030947 baseEnd_2030947 := by
    simpa [prefixWord, tailWord_2030947, baseEnd_2030947] using wordTrace_append hprefix tailTrace_2030947
  have hstable : (prefixWord ++ tailWord_2030947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030947).length < 2 ^ (prefixWord ++ tailWord_2030947).sum := by decide
  have hdescent : baseEnd_2030947 < baseStart_2030947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030953 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_2030953 : Nat := 118140960795 + 2030953 * 2 ^ 59
def prefixEnd_2030953 : Nat := 4983230072969 + 3 ^ 40 * 2030953 * 2
def baseEnd_2030953 : Nat := 1042855075690897620747323

theorem tailTrace_2030953 : CollatzResearch.WordTrace tailWord_2030953 prefixEnd_2030953 1042855075690897620747323 := by
  unfold tailWord_2030953
  simp only [CollatzResearch.WordTrace]
  refine ⟨74074941411211615002641513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49383294274141076668427675 74074941411211615002641513)
  ·
    refine ⟨55556206058408711251981135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74074941411211615002641513 55556206058408711251981135)
    ·
      refine ⟨83334309087613066877971703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55556206058408711251981135 83334309087613066877971703)
      ·
        refine ⟨125001463631419600316957555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83334309087613066877971703 125001463631419600316957555)
        ·
          refine ⟨187502195447129400475436333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125001463631419600316957555 187502195447129400475436333)
          ·
            refine ⟨70313323292673525178288625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187502195447129400475436333 70313323292673525178288625)
            ·
              refine ⟨52734992469505143883716469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70313323292673525178288625 52734992469505143883716469)
              ·
                refine ⟨4943905544016107239098419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52734992469505143883716469 4943905544016107239098419)
                ·
                  refine ⟨7415858316024160858647629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943905544016107239098419 7415858316024160858647629)
                  ·
                    refine ⟨2780946868509060321992861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7415858316024160858647629 2780946868509060321992861)
                    ·
                      refine ⟨1042855075690897620747323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780946868509060321992861 1042855075690897620747323)
                      ·
                        rfl

theorem cell23_2030953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_2030953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030953 prefixEnd_2030953 := by exact prefixLift 2030953
  have htrace : WordTrace (prefixWord ++ tailWord_2030953) baseStart_2030953 baseEnd_2030953 := by
    simpa [prefixWord, tailWord_2030953, baseEnd_2030953] using wordTrace_append hprefix tailTrace_2030953
  have hstable : (prefixWord ++ tailWord_2030953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030953).length < 2 ^ (prefixWord ++ tailWord_2030953).sum := by decide
  have hdescent : baseEnd_2030953 < baseStart_2030953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030957 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2030957 : Nat := 118140960795 + 2030957 * 2 ^ 59
def prefixEnd_2030957 : Nat := 4983230072969 + 3 ^ 40 * 2030957 * 2
def baseEnd_2030957 : Nat := 1042857129613515605097305

theorem tailTrace_2030957 : CollatzResearch.WordTrace tailWord_2030957 prefixEnd_2030957 1042857129613515605097305 := by
  unfold tailWord_2030957
  simp only [CollatzResearch.WordTrace]
  refine ⟨74075087303197123685787125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49383391535464749123858083 74075087303197123685787125)
  ·
    refine ⟨6944539434674730345542543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74075087303197123685787125 6944539434674730345542543)
    ·
      refine ⟨10416809152012095518313815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6944539434674730345542543 10416809152012095518313815)
      ·
        refine ⟨15625213728018143277470723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10416809152012095518313815 15625213728018143277470723)
        ·
          refine ⟨23437820592027214916206085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15625213728018143277470723 23437820592027214916206085)
          ·
            refine ⟨4394591361005102796788641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23437820592027214916206085 4394591361005102796788641)
            ·
              refine ⟨3295943520753827097591481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394591361005102796788641 3295943520753827097591481)
              ·
                refine ⟨2471957640565370323193611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3295943520753827097591481 2471957640565370323193611)
                ·
                  refine ⟨3707936460848055484790417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471957640565370323193611 3707936460848055484790417)
                  ·
                    refine ⟨2780952345636041613592813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3707936460848055484790417 2780952345636041613592813)
                    ·
                      refine ⟨1042857129613515605097305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2780952345636041613592813 1042857129613515605097305)
                      ·
                        rfl

theorem cell23_2030957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2030957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030957 prefixEnd_2030957 := by exact prefixLift 2030957
  have htrace : WordTrace (prefixWord ++ tailWord_2030957) baseStart_2030957 baseEnd_2030957 := by
    simpa [prefixWord, tailWord_2030957, baseEnd_2030957] using wordTrace_append hprefix tailTrace_2030957
  have hstable : (prefixWord ++ tailWord_2030957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030957).length < 2 ^ (prefixWord ++ tailWord_2030957).sum := by decide
  have hdescent : baseEnd_2030957 < baseStart_2030957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030974 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2030974 : Nat := 118140960795 + 2030974 * 2 ^ 59
def prefixEnd_2030974 : Nat := 4983230072969 + 3 ^ 40 * 2030974 * 2
def baseEnd_2030974 : Nat := 1042865858784642038584727

theorem tailTrace_2030974 : CollatzResearch.WordTrace tailWord_2030974 prefixEnd_2030974 1042865858784642038584727 := by
  unfold tailWord_2030974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259463418016941948644497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49383804896090357059437317 9259463418016941948644497)
  ·
    refine ⟨6944597563512706461483373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9259463418016941948644497 6944597563512706461483373)
    ·
      refine ⟨2604224086317264923056265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6944597563512706461483373 2604224086317264923056265)
      ·
        refine ⟨1953168064737948692292199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2604224086317264923056265 1953168064737948692292199)
        ·
          refine ⟨2929752097106923038438299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1953168064737948692292199 2929752097106923038438299)
          ·
            refine ⟨4394628145660384557657449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929752097106923038438299 4394628145660384557657449)
            ·
              refine ⟨3295971109245288418243087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394628145660384557657449 3295971109245288418243087)
              ·
                refine ⟨4943956663867932627364631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295971109245288418243087 4943956663867932627364631)
                ·
                  refine ⟨7415934995801898941046947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943956663867932627364631 7415934995801898941046947)
                  ·
                    refine ⟨11123902493702848411570421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7415934995801898941046947 11123902493702848411570421)
                    ·
                      refine ⟨1042865858784642038584727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11123902493702848411570421 1042865858784642038584727)
                      ·
                        rfl

theorem cell23_2030974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2030974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030974 prefixEnd_2030974 := by exact prefixLift 2030974
  have htrace : WordTrace (prefixWord ++ tailWord_2030974) baseStart_2030974 baseEnd_2030974 := by
    simpa [prefixWord, tailWord_2030974, baseEnd_2030974] using wordTrace_append hprefix tailTrace_2030974
  have hstable : (prefixWord ++ tailWord_2030974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030974).length < 2 ^ (prefixWord ++ tailWord_2030974).sum := by decide
  have hdescent : baseEnd_2030974 < baseStart_2030974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2030976 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2030976 : Nat := 118140960795 + 2030976 * 2 ^ 59
def prefixEnd_2030976 : Nat := 4983230072969 + 3 ^ 40 * 2030976 * 2
def baseEnd_2030976 : Nat := 1042866885745951030759717

theorem tailTrace_2030976 : CollatzResearch.WordTrace tailWord_2030976 prefixEnd_2030976 1042866885745951030759717 := by
  unfold tailWord_2030976
  simp only [CollatzResearch.WordTrace]
  refine ⟨37037890145064144965364391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49383853526752193287152521 37037890145064144965364391)
  ·
    refine ⟨55556835217596217448046587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37037890145064144965364391 55556835217596217448046587)
    ·
      refine ⟨83335252826394326172069881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55556835217596217448046587 83335252826394326172069881)
      ·
        refine ⟨62501439619795744629052411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83335252826394326172069881 62501439619795744629052411)
        ·
          refine ⟨93752159429693616943578617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62501439619795744629052411 93752159429693616943578617)
          ·
            refine ⟨70314119572270212707683963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93752159429693616943578617 70314119572270212707683963)
            ·
              refine ⟨105471179358405319061525945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70314119572270212707683963 105471179358405319061525945)
              ·
                refine ⟨79103384518803989296144459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105471179358405319061525945 79103384518803989296144459)
                ·
                  refine ⟨118655076778205983944216689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79103384518803989296144459 118655076778205983944216689)
                  ·
                    refine ⟨88991307583654487958162517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118655076778205983944216689 88991307583654487958162517)
                    ·
                      refine ⟨1042866885745951030759717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88991307583654487958162517 1042866885745951030759717)
                      ·
                        rfl

theorem cell23_2030976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2030976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2030976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2030976 prefixEnd_2030976 := by exact prefixLift 2030976
  have htrace : WordTrace (prefixWord ++ tailWord_2030976) baseStart_2030976 baseEnd_2030976 := by
    simpa [prefixWord, tailWord_2030976, baseEnd_2030976] using wordTrace_append hprefix tailTrace_2030976
  have hstable : (prefixWord ++ tailWord_2030976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2030976).length < 2 ^ (prefixWord ++ tailWord_2030976).sum := by decide
  have hdescent : baseEnd_2030976 < baseStart_2030976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2030976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031013 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_2031013 : Nat := 118140960795 + 2031013 * 2 ^ 59
def prefixEnd_2031013 : Nat := 4983230072969 + 3 ^ 40 * 2031013 * 2
def baseEnd_2031013 : Nat := 1042885884530167385997047

theorem tailTrace_2031013 : CollatzResearch.WordTrace tailWord_2031013 prefixEnd_2031013 1042885884530167385997047 := by
  unfold tailWord_2031013
  simp only [CollatzResearch.WordTrace]
  refine ⟨74077129790994245249825693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49384753193996163499883795 74077129790994245249825693)
  ·
    refine ⟨27778923671622841968684635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74077129790994245249825693 27778923671622841968684635)
    ·
      refine ⟨41668385507434262953026953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27778923671622841968684635 41668385507434262953026953)
      ·
        refine ⟨31251289130575697214770215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41668385507434262953026953 31251289130575697214770215)
        ·
          refine ⟨46876933695863545822155323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31251289130575697214770215 46876933695863545822155323)
          ·
            refine ⟨70315400543795318733232985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46876933695863545822155323 70315400543795318733232985)
            ·
              refine ⟨52736550407846489049924739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70315400543795318733232985 52736550407846489049924739)
              ·
                refine ⟨79104825611769733574887109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52736550407846489049924739 79104825611769733574887109)
                ·
                  refine ⟨14832154802206825045291333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79104825611769733574887109 14832154802206825045291333)
                  ·
                    refine ⟨2781029025413779695992125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14832154802206825045291333 2781029025413779695992125)
                    ·
                      refine ⟨1042885884530167385997047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2781029025413779695992125 1042885884530167385997047)
                      ·
                        rfl

theorem cell23_2031013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_2031013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031013 prefixEnd_2031013 := by exact prefixLift 2031013
  have htrace : WordTrace (prefixWord ++ tailWord_2031013) baseStart_2031013 baseEnd_2031013 := by
    simpa [prefixWord, tailWord_2031013, baseEnd_2031013] using wordTrace_append hprefix tailTrace_2031013
  have hstable : (prefixWord ++ tailWord_2031013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031013).length < 2 ^ (prefixWord ++ tailWord_2031013).sum := by decide
  have hdescent : baseEnd_2031013 < baseStart_2031013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031063 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 4, 5]
def baseStart_2031063 : Nat := 118140960795 + 2031063 * 2 ^ 59
def prefixEnd_2031063 : Nat := 4983230072969 + 3 ^ 40 * 2031063 * 2
def baseEnd_2031063 : Nat := 347637186187630730123939

theorem tailTrace_2031063 : CollatzResearch.WordTrace tailWord_2031063 prefixEnd_2031063 347637186187630730123939 := by
  unfold tailWord_2031063
  simp only [CollatzResearch.WordTrace]
  refine ⟨74078953440813103789145843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49385968960542069192763895 74078953440813103789145843)
  ·
    refine ⟨111118430161219655683718765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74078953440813103789145843 111118430161219655683718765)
    ·
      refine ⟨41669411310457370881394537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111118430161219655683718765 41669411310457370881394537)
      ·
        refine ⟨31252058482843028161045903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41669411310457370881394537 31252058482843028161045903)
        ·
          refine ⟨46878087724264542241568855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31252058482843028161045903 46878087724264542241568855)
          ·
            refine ⟨70317131586396813362353283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46878087724264542241568855 70317131586396813362353283)
            ·
              refine ⟨105475697379595220043529925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70317131586396813362353283 105475697379595220043529925)
              ·
                refine ⟨19776693258674103758161861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105475697379595220043529925 19776693258674103758161861)
                ·
                  refine ⟨3708129986001394454655349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19776693258674103758161861 3708129986001394454655349)
                  ·
                    refine ⟨347637186187630730123939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3708129986001394454655349 347637186187630730123939)
                    ·
                      rfl

theorem cell23_2031063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_2031063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031063 prefixEnd_2031063 := by exact prefixLift 2031063
  have htrace : WordTrace (prefixWord ++ tailWord_2031063) baseStart_2031063 baseEnd_2031063 := by
    simpa [prefixWord, tailWord_2031063, baseEnd_2031063] using wordTrace_append hprefix tailTrace_2031063
  have hstable : (prefixWord ++ tailWord_2031063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031063).length < 2 ^ (prefixWord ++ tailWord_2031063).sum := by decide
  have hdescent : baseEnd_2031063 < baseStart_2031063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031100 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_2031100 : Nat := 118140960795 + 2031100 * 2 ^ 59
def prefixEnd_2031100 : Nat := 4983230072969 + 3 ^ 40 * 2031100 * 2
def baseEnd_2031100 : Nat := 1042930557347108545609147

theorem tailTrace_2031100 : CollatzResearch.WordTrace tailWord_2031100 prefixEnd_2031100 1042930557347108545609147 := by
  unfold tailWord_2031100
  simp only [CollatzResearch.WordTrace]
  refine ⟨37040151470839529554121377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49386868627786039405495169 37040151470839529554121377)
  ·
    refine ⟨27780113603129647165591033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37040151470839529554121377 27780113603129647165591033)
    ·
      refine ⟨20835085202347235374193275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27780113603129647165591033 20835085202347235374193275)
      ·
        refine ⟨31252627803520853061289913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20835085202347235374193275 31252627803520853061289913)
        ·
          refine ⟨23439470852640639795967435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31252627803520853061289913 23439470852640639795967435)
          ·
            refine ⟨35159206278960959693951153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23439470852640639795967435 35159206278960959693951153)
            ·
              refine ⟨26369404709220719770463365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35159206278960959693951153 26369404709220719770463365)
              ·
                refine ⟨4944263382978884956961881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26369404709220719770463365 4944263382978884956961881)
                ·
                  refine ⟨3708197537234163717721411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944263382978884956961881 3708197537234163717721411)
                  ·
                    refine ⟨5562296305851245576582117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708197537234163717721411 5562296305851245576582117)
                    ·
                      refine ⟨1042930557347108545609147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5562296305851245576582117 1042930557347108545609147)
                      ·
                        rfl

theorem cell23_2031100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_2031100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031100 prefixEnd_2031100 := by exact prefixLift 2031100
  have htrace : WordTrace (prefixWord ++ tailWord_2031100) baseStart_2031100 baseEnd_2031100 := by
    simpa [prefixWord, tailWord_2031100, baseEnd_2031100] using wordTrace_append hprefix tailTrace_2031100
  have hstable : (prefixWord ++ tailWord_2031100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031100).length < 2 ^ (prefixWord ++ tailWord_2031100).sum := by decide
  have hdescent : baseEnd_2031100 < baseStart_2031100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031113 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_2031113 : Nat := 118140960795 + 2031113 * 2 ^ 59
def prefixEnd_2031113 : Nat := 4983230072969 + 3 ^ 40 * 2031113 * 2
def baseEnd_2031113 : Nat := 1042937232595616994746587

theorem tailTrace_2031113 : CollatzResearch.WordTrace tailWord_2031113 prefixEnd_2031113 1042937232595616994746587 := by
  unfold tailWord_2031113
  simp only [CollatzResearch.WordTrace]
  refine ⟨74080777090631962328465993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49387184727087974885643995 74080777090631962328465993)
  ·
    refine ⟨55560582817973971746349495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74080777090631962328465993 55560582817973971746349495)
    ·
      refine ⟨83340874226960957619524243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55560582817973971746349495 83340874226960957619524243)
      ·
        refine ⟨125011311340441436429286365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83340874226960957619524243 125011311340441436429286365)
        ·
          refine ⟨46879241752665538660982387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125011311340441436429286365 46879241752665538660982387)
          ·
            refine ⟨70318862628998307991473581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46879241752665538660982387 70318862628998307991473581)
            ·
              refine ⟨26369573485874365496802593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70318862628998307991473581 26369573485874365496802593)
              ·
                refine ⟨19777180114405774122601945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26369573485874365496802593 19777180114405774122601945)
                ·
                  refine ⟨14832885085804330591951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19777180114405774122601945 14832885085804330591951459)
                  ·
                    refine ⟨22249327628706495887927189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14832885085804330591951459 22249327628706495887927189)
                    ·
                      refine ⟨1042937232595616994746587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22249327628706495887927189 1042937232595616994746587)
                      ·
                        rfl

theorem cell23_2031113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_2031113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031113 prefixEnd_2031113 := by exact prefixLift 2031113
  have htrace : WordTrace (prefixWord ++ tailWord_2031113) baseStart_2031113 baseEnd_2031113 := by
    simpa [prefixWord, tailWord_2031113, baseEnd_2031113] using wordTrace_append hprefix tailTrace_2031113
  have hstable : (prefixWord ++ tailWord_2031113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031113).length < 2 ^ (prefixWord ++ tailWord_2031113).sum := by decide
  have hdescent : baseEnd_2031113 < baseStart_2031113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031161 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 1, 4]
def baseStart_2031161 : Nat := 118140960795 + 2031161 * 2 ^ 59
def prefixEnd_2031161 : Nat := 4983230072969 + 3 ^ 40 * 2031161 * 2
def baseEnd_2031161 : Nat := 347653959889010935648789

theorem tailTrace_2031161 : CollatzResearch.WordTrace tailWord_2031161 prefixEnd_2031161 347653959889010935648789 := by
  unfold tailWord_2031161
  simp only [CollatzResearch.WordTrace]
  refine ⟨74082527794458066526213337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49388351862972044350808891 74082527794458066526213337)
  ·
    refine ⟨55561895845843549894660003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74082527794458066526213337 55561895845843549894660003)
    ·
      refine ⟨83342843768765324841990005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55561895845843549894660003 83342843768765324841990005)
      ·
        refine ⟨7813391603321749203936563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83342843768765324841990005 7813391603321749203936563)
        ·
          refine ⟨11720087404982623805904845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813391603321749203936563 11720087404982623805904845)
          ·
            refine ⟨4395032776868483927214317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11720087404982623805904845 4395032776868483927214317)
            ·
              refine ⟨1648137291325681472705369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4395032776868483927214317 1648137291325681472705369)
              ·
                refine ⟨1236102968494261104529027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648137291325681472705369 1236102968494261104529027)
                ·
                  refine ⟨1854154452741391656793541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236102968494261104529027 1854154452741391656793541)
                  ·
                    refine ⟨347653959889010935648789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1854154452741391656793541 347653959889010935648789)
                    ·
                      rfl

theorem cell23_2031161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 4].length) (baseStart_2031161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031161 prefixEnd_2031161 := by exact prefixLift 2031161
  have htrace : WordTrace (prefixWord ++ tailWord_2031161) baseStart_2031161 baseEnd_2031161 := by
    simpa [prefixWord, tailWord_2031161, baseEnd_2031161] using wordTrace_append hprefix tailTrace_2031161
  have hstable : (prefixWord ++ tailWord_2031161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031161).length < 2 ^ (prefixWord ++ tailWord_2031161).sum := by decide
  have hdescent : baseEnd_2031161 < baseStart_2031161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031204 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_2031204 : Nat := 118140960795 + 2031204 * 2 ^ 59
def prefixEnd_2031204 : Nat := 4983230072969 + 3 ^ 40 * 2031204 * 2
def baseEnd_2031204 : Nat := 347661319778392046236223

theorem tailTrace_2031204 : CollatzResearch.WordTrace tailWord_2031204 prefixEnd_2031204 347661319778392046236223 := by
  unfold tailWord_2031204
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042048066651142435014333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49389397422201523246685777 37042048066651142435014333)
  ·
    refine ⟨13890768024994178413130375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37042048066651142435014333 13890768024994178413130375)
    ·
      refine ⟨20836152037491267619695563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890768024994178413130375 20836152037491267619695563)
      ·
        refine ⟨31254228056236901429543345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20836152037491267619695563 31254228056236901429543345)
        ·
          refine ⟨23440671042177676072157509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31254228056236901429543345 23440671042177676072157509)
          ·
            refine ⟨4395125820408314263529533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23440671042177676072157509 4395125820408314263529533)
            ·
              refine ⟨1648172182653117848823575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4395125820408314263529533 1648172182653117848823575)
              ·
                refine ⟨2472258273979676773235363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648172182653117848823575 2472258273979676773235363)
                ·
                  refine ⟨3708387410969515159853045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472258273979676773235363 3708387410969515159853045)
                  ·
                    refine ⟨347661319778392046236223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3708387410969515159853045 347661319778392046236223)
                    ·
                      rfl

theorem cell23_2031204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_2031204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031204 prefixEnd_2031204 := by exact prefixLift 2031204
  have htrace : WordTrace (prefixWord ++ tailWord_2031204) baseStart_2031204 baseEnd_2031204 := by
    simpa [prefixWord, tailWord_2031204, baseEnd_2031204] using wordTrace_append hprefix tailTrace_2031204
  have hstable : (prefixWord ++ tailWord_2031204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031204).length < 2 ^ (prefixWord ++ tailWord_2031204).sum := by decide
  have hdescent : baseEnd_2031204 < baseStart_2031204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031207 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2031207 : Nat := 118140960795 + 2031207 * 2 ^ 59
def prefixEnd_2031207 : Nat := 4983230072969 + 3 ^ 40 * 2031207 * 2
def baseEnd_2031207 : Nat := 1042985499777139626971155

theorem tailTrace_2031207 : CollatzResearch.WordTrace tailWord_2031207 prefixEnd_2031207 1042985499777139626971155 := by
  unfold tailWord_2031207
  simp only [CollatzResearch.WordTrace]
  refine ⟨74084205552291416382387875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49389470368194277588258583 74084205552291416382387875)
  ·
    refine ⟨111126308328437124573581813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74084205552291416382387875 111126308328437124573581813)
    ·
      refine ⟨10418091405790980428773295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111126308328437124573581813 10418091405790980428773295)
      ·
        refine ⟨15627137108686470643159943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418091405790980428773295 15627137108686470643159943)
        ·
          refine ⟨23440705663029705964739915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627137108686470643159943 23440705663029705964739915)
          ·
            refine ⟨35161058494544558947109873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23440705663029705964739915 35161058494544558947109873)
            ·
              refine ⟨26370793870908419210332405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35161058494544558947109873 26370793870908419210332405)
              ·
                refine ⟨2472261925397664300968663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26370793870908419210332405 2472261925397664300968663)
                ·
                  refine ⟨3708392888096496451452995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472261925397664300968663 3708392888096496451452995)
                  ·
                    refine ⟨5562589332144744677179493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708392888096496451452995 5562589332144744677179493)
                    ·
                      refine ⟨1042985499777139626971155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5562589332144744677179493 1042985499777139626971155)
                      ·
                        rfl

theorem cell23_2031207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2031207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031207 prefixEnd_2031207 := by exact prefixLift 2031207
  have htrace : WordTrace (prefixWord ++ tailWord_2031207) baseStart_2031207 baseEnd_2031207 := by
    simpa [prefixWord, tailWord_2031207, baseEnd_2031207] using wordTrace_append hprefix tailTrace_2031207
  have hstable : (prefixWord ++ tailWord_2031207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031207).length < 2 ^ (prefixWord ++ tailWord_2031207).sum := by decide
  have hdescent : baseEnd_2031207 < baseStart_2031207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031218 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2031218 : Nat := 118140960795 + 2031218 * 2 ^ 59
def prefixEnd_2031218 : Nat := 4983230072969 + 3 ^ 40 * 2031218 * 2
def baseEnd_2031218 : Nat := 1042991148064339083933605

theorem tailTrace_2031218 : CollatzResearch.WordTrace tailWord_2031218 prefixEnd_2031218 1042991148064339083933605 := by
  unfold tailWord_2031218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521151688812891315259577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49389737836834376840692205 18521151688812891315259577)
  ·
    refine ⟨13890863766609668486444683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18521151688812891315259577 13890863766609668486444683)
    ·
      refine ⟨20836295649914502729667025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890863766609668486444683 20836295649914502729667025)
      ·
        refine ⟨15627221737435877047250269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20836295649914502729667025 15627221737435877047250269)
        ·
          refine ⟨5860208151538453892718851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15627221737435877047250269 5860208151538453892718851)
          ·
            refine ⟨8790312227307680839078277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860208151538453892718851 8790312227307680839078277)
            ·
              refine ⟨1648183542620190157327177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8790312227307680839078277 1648183542620190157327177)
              ·
                refine ⟨1236137656965142617995383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648183542620190157327177 1236137656965142617995383)
                ·
                  refine ⟨1854206485447713926993075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236137656965142617995383 1854206485447713926993075)
                  ·
                    refine ⟨2781309728171570890489613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1854206485447713926993075 2781309728171570890489613)
                    ·
                      refine ⟨1042991148064339083933605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2781309728171570890489613 1042991148064339083933605)
                      ·
                        rfl

theorem cell23_2031218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2031218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031218 prefixEnd_2031218 := by exact prefixLift 2031218
  have htrace : WordTrace (prefixWord ++ tailWord_2031218) baseStart_2031218 baseEnd_2031218 := by
    simpa [prefixWord, tailWord_2031218, baseEnd_2031218] using wordTrace_append hprefix tailTrace_2031218
  have hstable : (prefixWord ++ tailWord_2031218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031218).length < 2 ^ (prefixWord ++ tailWord_2031218).sum := by decide
  have hdescent : baseEnd_2031218 < baseStart_2031218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031237 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_2031237 : Nat := 118140960795 + 2031237 * 2 ^ 59
def prefixEnd_2031237 : Nat := 4983230072969 + 3 ^ 40 * 2031237 * 2
def baseEnd_2031237 : Nat := 1043000904196774509596017

theorem tailTrace_2031237 : CollatzResearch.WordTrace tailWord_2031237 prefixEnd_2031237 1043000904196774509596017 := by
  unfold tailWord_2031237
  simp only [CollatzResearch.WordTrace]
  refine ⟨74085299742182731505979965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49390199828121821003986643 74085299742182731505979965)
  ·
    refine ⟨27781987403318524314742487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74085299742182731505979965 27781987403318524314742487)
    ·
      refine ⟨41672981104977786472113731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27781987403318524314742487 41672981104977786472113731)
      ·
        refine ⟨62509471657466679708170597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41672981104977786472113731 62509471657466679708170597)
        ·
          refine ⟨11720525935775002445281987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62509471657466679708170597 11720525935775002445281987)
          ·
            refine ⟨17580788903662503667922981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720525935775002445281987 17580788903662503667922981)
            ·
              refine ⟨3296397919436719437735559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17580788903662503667922981 3296397919436719437735559)
              ·
                refine ⟨4944596879155079156603339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296397919436719437735559 4944596879155079156603339)
                ·
                  refine ⟨7416895318732618734905009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944596879155079156603339 7416895318732618734905009)
                  ·
                    refine ⟨5562671489049464051178757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416895318732618734905009 5562671489049464051178757)
                    ·
                      refine ⟨1043000904196774509596017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5562671489049464051178757 1043000904196774509596017)
                      ·
                        rfl

theorem cell23_2031237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_2031237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031237 prefixEnd_2031237 := by exact prefixLift 2031237
  have htrace : WordTrace (prefixWord ++ tailWord_2031237) baseStart_2031237 baseEnd_2031237 := by
    simpa [prefixWord, tailWord_2031237, baseEnd_2031237] using wordTrace_append hprefix tailTrace_2031237
  have hstable : (prefixWord ++ tailWord_2031237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031237).length < 2 ^ (prefixWord ++ tailWord_2031237).sum := by decide
  have hdescent : baseEnd_2031237 < baseStart_2031237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031280 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_2031280 : Nat := 118140960795 + 2031280 * 2 ^ 59
def prefixEnd_2031280 : Nat := 4983230072969 + 3 ^ 40 * 2031280 * 2
def baseEnd_2031280 : Nat := 1043022983864917841358319

theorem tailTrace_2031280 : CollatzResearch.WordTrace tailWord_2031280 prefixEnd_2031280 1043022983864917841358319 := by
  unfold tailWord_2031280
  simp only [CollatzResearch.WordTrace]
  refine ⟨37043434040513474924897647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49391245387351299899863529 37043434040513474924897647)
  ·
    refine ⟨55565151060770212387346471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37043434040513474924897647 55565151060770212387346471)
    ·
      refine ⟨83347726591155318581019707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55565151060770212387346471 83347726591155318581019707)
      ·
        refine ⟨125021589886732977871529561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83347726591155318581019707 125021589886732977871529561)
        ·
          refine ⟨93766192415049733403647171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125021589886732977871529561 93766192415049733403647171)
          ·
            refine ⟨140649288622574600105470757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93766192415049733403647171 140649288622574600105470757)
            ·
              refine ⟨26371741616732737519775767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140649288622574600105470757 26371741616732737519775767)
              ·
                refine ⟨39557612425099106279663651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26371741616732737519775767 39557612425099106279663651)
                ·
                  refine ⟨59336418637648659419495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39557612425099106279663651 59336418637648659419495477)
                  ·
                    refine ⟨5562789247279561820577701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59336418637648659419495477 5562789247279561820577701)
                    ·
                      refine ⟨1043022983864917841358319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5562789247279561820577701 1043022983864917841358319)
                      ·
                        rfl

theorem cell23_2031280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_2031280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031280 prefixEnd_2031280 := by exact prefixLift 2031280
  have htrace : WordTrace (prefixWord ++ tailWord_2031280) baseStart_2031280 baseEnd_2031280 := by
    simpa [prefixWord, tailWord_2031280, baseEnd_2031280] using wordTrace_append hprefix tailTrace_2031280
  have hstable : (prefixWord ++ tailWord_2031280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031280).length < 2 ^ (prefixWord ++ tailWord_2031280).sum := by decide
  have hdescent : baseEnd_2031280 < baseStart_2031280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031347 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3]
def baseStart_2031347 : Nat := 118140960795 + 2031347 * 2 ^ 59
def prefixEnd_2031347 : Nat := 4983230072969 + 3 ^ 40 * 2031347 * 2
def baseEnd_2031347 : Nat := 1043057387068769079220511

theorem tailTrace_2031347 : CollatzResearch.WordTrace tailWord_2031347 prefixEnd_2031347 1043057387068769079220511 := by
  unfold tailWord_2031347
  simp only [CollatzResearch.WordTrace]
  refine ⟨74089311771784220292484295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49392874514522813528322863 74089311771784220292484295)
  ·
    refine ⟨111133967657676330438726443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74089311771784220292484295 111133967657676330438726443)
    ·
      refine ⟨166700951486514495658089665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111133967657676330438726443 166700951486514495658089665)
      ·
        refine ⟨125025713614885871743567249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166700951486514495658089665 125025713614885871743567249)
        ·
          refine ⟨93769285211164403807675437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125025713614885871743567249 93769285211164403807675437)
          ·
            refine ⟨35163481954186651427878289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93769285211164403807675437 35163481954186651427878289)
            ·
              refine ⟨26372611465639988570908717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35163481954186651427878289 26372611465639988570908717)
              ·
                refine ⟨9889729299614995714090769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26372611465639988570908717 9889729299614995714090769)
                ·
                  refine ⟨7417296974711246785568077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9889729299614995714090769 7417296974711246785568077)
                  ·
                    refine ⟨2781486365516717544588029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7417296974711246785568077 2781486365516717544588029)
                    ·
                      refine ⟨1043057387068769079220511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2781486365516717544588029 1043057387068769079220511)
                      ·
                        rfl

theorem cell23_2031347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_2031347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031347 prefixEnd_2031347 := by exact prefixLift 2031347
  have htrace : WordTrace (prefixWord ++ tailWord_2031347) baseStart_2031347 baseEnd_2031347 := by
    simpa [prefixWord, tailWord_2031347, baseEnd_2031347] using wordTrace_append hprefix tailTrace_2031347
  have hstable : (prefixWord ++ tailWord_2031347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031347).length < 2 ^ (prefixWord ++ tailWord_2031347).sum := by decide
  have hdescent : baseEnd_2031347 < baseStart_2031347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031404 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_2031404 : Nat := 118140960795 + 2031404 * 2 ^ 59
def prefixEnd_2031404 : Nat := 4983230072969 + 3 ^ 40 * 2031404 * 2
def baseEnd_2031404 : Nat := 1043086655466075356207749

theorem tailTrace_2031404 : CollatzResearch.WordTrace tailWord_2031404 prefixEnd_2031404 1043086655466075356207749 := by
  unfold tailWord_2031404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37045695366288859513654633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49394260488385146018206177 37045695366288859513654633)
  ·
    refine ⟨27784271524716644635240975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37045695366288859513654633 27784271524716644635240975)
    ·
      refine ⟨41676407287074966952861463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27784271524716644635240975 41676407287074966952861463)
      ·
        refine ⟨62514610930612450429292195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41676407287074966952861463 62514610930612450429292195)
        ·
          refine ⟨93771916395918675643938293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62514610930612450429292195 93771916395918675643938293)
          ·
            refine ⟨8791117162117375841619215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93771916395918675643938293 8791117162117375841619215)
            ·
              refine ⟨13186675743176063762428823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8791117162117375841619215 13186675743176063762428823)
              ·
                refine ⟨19780013614764095643643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13186675743176063762428823 19780013614764095643643235)
                ·
                  refine ⟨29670020422146143465464853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19780013614764095643643235 29670020422146143465464853)
                  ·
                    refine ⟨1390782207288100474943665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29670020422146143465464853 1390782207288100474943665)
                    ·
                      refine ⟨1043086655466075356207749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390782207288100474943665 1043086655466075356207749)
                      ·
                        rfl

theorem cell23_2031404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_2031404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031404 prefixEnd_2031404 := by exact prefixLift 2031404
  have htrace : WordTrace (prefixWord ++ tailWord_2031404) baseStart_2031404 baseEnd_2031404 := by
    simpa [prefixWord, tailWord_2031404, baseEnd_2031404] using wordTrace_append hprefix tailTrace_2031404
  have hstable : (prefixWord ++ tailWord_2031404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031404).length < 2 ^ (prefixWord ++ tailWord_2031404).sum := by decide
  have hdescent : baseEnd_2031404 < baseStart_2031404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031407 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_2031407 : Nat := 118140960795 + 2031407 * 2 ^ 59
def prefixEnd_2031407 : Nat := 4983230072969 + 3 ^ 40 * 2031407 * 2
def baseEnd_2031407 : Nat := 1043088195908038844470235

theorem tailTrace_2031407 : CollatzResearch.WordTrace tailWord_2031407 prefixEnd_2031407 1043088195908038844470235 := by
  unfold tailWord_2031407
  simp only [CollatzResearch.WordTrace]
  refine ⟨74091500151566850539668475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49394333434377900359778983 74091500151566850539668475)
  ·
    refine ⟨111137250227350275809502713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74091500151566850539668475 111137250227350275809502713)
    ·
      refine ⟨83352937670512706857127035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111137250227350275809502713 83352937670512706857127035)
      ·
        refine ⟨125029406505769060285690553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83352937670512706857127035 125029406505769060285690553)
        ·
          refine ⟨93772054879326795214267915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125029406505769060285690553 93772054879326795214267915)
          ·
            refine ⟨140658082318990192821401873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93772054879326795214267915 140658082318990192821401873)
            ·
              refine ⟨105493561739242644616051405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140658082318990192821401873 105493561739242644616051405)
              ·
                refine ⟨39560085652215991731019277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105493561739242644616051405 39560085652215991731019277)
                ·
                  refine ⟨14835032119580996899132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39560085652215991731019277 14835032119580996899132229)
                  ·
                    refine ⟨2781568522421436918587293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14835032119580996899132229 2781568522421436918587293)
                    ·
                      refine ⟨1043088195908038844470235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2781568522421436918587293 1043088195908038844470235)
                      ·
                        rfl

theorem cell23_2031407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_2031407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031407 prefixEnd_2031407 := by exact prefixLift 2031407
  have htrace : WordTrace (prefixWord ++ tailWord_2031407) baseStart_2031407 baseEnd_2031407 := by
    simpa [prefixWord, tailWord_2031407, baseEnd_2031407] using wordTrace_append hprefix tailTrace_2031407
  have hstable : (prefixWord ++ tailWord_2031407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031407).length < 2 ^ (prefixWord ++ tailWord_2031407).sum := by decide
  have hdescent : baseEnd_2031407 < baseStart_2031407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031421 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2031421 : Nat := 118140960795 + 2031421 * 2 ^ 59
def prefixEnd_2031421 : Nat := 4983230072969 + 3 ^ 40 * 2031421 * 2
def baseEnd_2031421 : Nat := 1043095384637201789695171

theorem tailTrace_2031421 : CollatzResearch.WordTrace tailWord_2031421 prefixEnd_2031421 1043095384637201789695171 := by
  unfold tailWord_2031421
  simp only [CollatzResearch.WordTrace]
  refine ⟨74092010773516130930678117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49394673849010753953785411 74092010773516130930678117)
  ·
    refine ⟨13892252020034274549502147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74092010773516130930678117 13892252020034274549502147)
    ·
      refine ⟨20838378030051411824253221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892252020034274549502147 20838378030051411824253221)
      ·
        refine ⟨3907195880634639717047479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20838378030051411824253221 3907195880634639717047479)
        ·
          refine ⟨5860793820951959575571219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907195880634639717047479 5860793820951959575571219)
          ·
            refine ⟨8791190731427939363356829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860793820951959575571219 8791190731427939363356829)
            ·
              refine ⟨3296696524285477261258811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8791190731427939363356829 3296696524285477261258811)
              ·
                refine ⟨4945044786428215891888217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296696524285477261258811 4945044786428215891888217)
                ·
                  refine ⟨3708783589821161918916163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945044786428215891888217 3708783589821161918916163)
                  ·
                    refine ⟨5563175384731742878374245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708783589821161918916163 5563175384731742878374245)
                    ·
                      refine ⟨1043095384637201789695171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5563175384731742878374245 1043095384637201789695171)
                      ·
                        rfl

theorem cell23_2031421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2031421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031421 prefixEnd_2031421 := by exact prefixLift 2031421
  have htrace : WordTrace (prefixWord ++ tailWord_2031421) baseStart_2031421 baseEnd_2031421 := by
    simpa [prefixWord, tailWord_2031421, baseEnd_2031421] using wordTrace_append hprefix tailTrace_2031421
  have hstable : (prefixWord ++ tailWord_2031421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031421).length < 2 ^ (prefixWord ++ tailWord_2031421).sum := by decide
  have hdescent : baseEnd_2031421 < baseStart_2031421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031431 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 1, 4]
def baseStart_2031431 : Nat := 118140960795 + 2031431 * 2 ^ 59
def prefixEnd_2031431 : Nat := 4983230072969 + 3 ^ 40 * 2031431 * 2
def baseEnd_2031431 : Nat := 347700173147915583523375

theorem tailTrace_2031431 : CollatzResearch.WordTrace tailWord_2031431 prefixEnd_2031431 347700173147915583523375 := by
  unfold tailWord_2031431
  simp only [CollatzResearch.WordTrace]
  refine ⟨74092375503479902638542147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49394917002319935092361431 74092375503479902638542147)
  ·
    refine ⟨111138563255219853957813221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74092375503479902638542147 111138563255219853957813221)
    ·
      refine ⟨20838480610353722617089979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111138563255219853957813221 20838480610353722617089979)
      ·
        refine ⟨31257720915530583925634969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838480610353722617089979 31257720915530583925634969)
        ·
          refine ⟨23443290686647937944226227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31257720915530583925634969 23443290686647937944226227)
          ·
            refine ⟨35164936029971906916339341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23443290686647937944226227 35164936029971906916339341)
            ·
              refine ⟨13186851011239465093627253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35164936029971906916339341 13186851011239465093627253)
              ·
                refine ⟨1236267282303699852527555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13186851011239465093627253 1236267282303699852527555)
                ·
                  refine ⟨1854400923455549778791333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236267282303699852527555 1854400923455549778791333)
                  ·
                    refine ⟨347700173147915583523375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1854400923455549778791333 347700173147915583523375)
                    ·
                      rfl

theorem cell23_2031431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_2031431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031431 prefixEnd_2031431 := by exact prefixLift 2031431
  have htrace : WordTrace (prefixWord ++ tailWord_2031431) baseStart_2031431 baseEnd_2031431 := by
    simpa [prefixWord, tailWord_2031431, baseEnd_2031431] using wordTrace_append hprefix tailTrace_2031431
  have hstable : (prefixWord ++ tailWord_2031431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031431).length < 2 ^ (prefixWord ++ tailWord_2031431).sum := by decide
  have hdescent : baseEnd_2031431 < baseStart_2031431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031444 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 8]
def baseStart_2031444 : Nat := 118140960795 + 2031444 * 2 ^ 59
def prefixEnd_2031444 : Nat := 4983230072969 + 3 ^ 40 * 2031444 * 2
def baseEnd_2031444 : Nat := 115900799410250577745285

theorem tailTrace_2031444 : CollatzResearch.WordTrace tailWord_2031444 prefixEnd_2031444 115900799410250577745285 := by
  unfold tailWord_2031444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37046424826216402929382693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49395233101621870572510257 37046424826216402929382693)
  ·
    refine ⟨6946204654915575549259255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37046424826216402929382693 6946204654915575549259255)
    ·
      refine ⟨10419306982373363323888883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946204654915575549259255 10419306982373363323888883)
      ·
        refine ⟨15628960473560044985833325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419306982373363323888883 15628960473560044985833325)
        ·
          refine ⟨5860860177585016869687497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15628960473560044985833325 5860860177585016869687497)
          ·
            refine ⟨4395645133188762652265623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5860860177585016869687497 4395645133188762652265623)
            ·
              refine ⟨6593467699783143978398435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395645133188762652265623 6593467699783143978398435)
              ·
                refine ⟨9890201549674715967597653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593467699783143978398435 9890201549674715967597653)
                ·
                  refine ⟨115900799410250577745285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9890201549674715967597653 115900799410250577745285)
                  ·
                    rfl

theorem cell23_2031444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_2031444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031444 prefixEnd_2031444 := by exact prefixLift 2031444
  have htrace : WordTrace (prefixWord ++ tailWord_2031444) baseStart_2031444 baseEnd_2031444 := by
    simpa [prefixWord, tailWord_2031444, baseEnd_2031444] using wordTrace_append hprefix tailTrace_2031444
  have hstable : (prefixWord ++ tailWord_2031444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031444).length < 2 ^ (prefixWord ++ tailWord_2031444).sum := by decide
  have hdescent : baseEnd_2031444 < baseStart_2031444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031481 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 2, 3, 2]
def baseStart_2031481 : Nat := 118140960795 + 2031481 * 2 ^ 59
def prefixEnd_2031481 : Nat := 4983230072969 + 3 ^ 40 * 2031481 * 2
def baseEnd_2031481 : Nat := 1043126193476471554944895

theorem tailTrace_2031481 : CollatzResearch.WordTrace tailWord_2031481 prefixEnd_2031481 1043126193476471554944895 := by
  unfold tailWord_2031481
  simp only [CollatzResearch.WordTrace]
  refine ⟨74094199153298761177862297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49396132768865840785241531 74094199153298761177862297)
  ·
    refine ⟨55570649364974070883396723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74094199153298761177862297 55570649364974070883396723)
    ·
      refine ⟨83355974047461106325095085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55570649364974070883396723 83355974047461106325095085)
      ·
        refine ⟨31258490267797914871910657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83355974047461106325095085 31258490267797914871910657)
        ·
          refine ⟨23443867700848436153932993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31258490267797914871910657 23443867700848436153932993)
          ·
            refine ⟨17582900775636327115449745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23443867700848436153932993 17582900775636327115449745)
            ·
              refine ⟨13187175581727245336587309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17582900775636327115449745 13187175581727245336587309)
              ·
                refine ⟨4945190843147717001220241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13187175581727245336587309 4945190843147717001220241)
                ·
                  refine ⟨3708893132360787750915181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945190843147717001220241 3708893132360787750915181)
                  ·
                    refine ⟨1390834924635295406593193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708893132360787750915181 1390834924635295406593193)
                    ·
                      refine ⟨1043126193476471554944895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390834924635295406593193 1043126193476471554944895)
                      ·
                        rfl

theorem cell23_2031481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_2031481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031481 prefixEnd_2031481 := by exact prefixLift 2031481
  have htrace : WordTrace (prefixWord ++ tailWord_2031481) baseStart_2031481 baseEnd_2031481 := by
    simpa [prefixWord, tailWord_2031481, baseEnd_2031481] using wordTrace_append hprefix tailTrace_2031481
  have hstable : (prefixWord ++ tailWord_2031481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031481).length < 2 ^ (prefixWord ++ tailWord_2031481).sum := by decide
  have hdescent : baseEnd_2031481 < baseStart_2031481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031487 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 3, 6]
def baseStart_2031487 : Nat := 118140960795 + 2031487 * 2 ^ 59
def prefixEnd_2031487 : Nat := 4983230072969 + 3 ^ 40 * 2031487 * 2
def baseEnd_2031487 : Nat := 347709758120132843823289

theorem tailTrace_2031487 : CollatzResearch.WordTrace tailWord_2031487 prefixEnd_2031487 347709758120132843823289 := by
  unfold tailWord_2031487
  simp only [CollatzResearch.WordTrace]
  refine ⟨74094417991277024202580715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49396278660851349468387143 74094417991277024202580715)
  ·
    refine ⟨111141626986915536303871073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74094417991277024202580715 111141626986915536303871073)
    ·
      refine ⟨83356220240186652227903305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111141626986915536303871073 83356220240186652227903305)
      ·
        refine ⟨62517165180139989170927479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83356220240186652227903305 62517165180139989170927479)
        ·
          refine ⟨93775747770209983756391219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62517165180139989170927479 93775747770209983756391219)
          ·
            refine ⟨140663621655314975634586829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93775747770209983756391219 140663621655314975634586829)
            ·
              refine ⟨52748858120743115862970061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140663621655314975634586829 52748858120743115862970061)
              ·
                refine ⟨19780821795278668448613773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52748858120743115862970061 19780821795278668448613773)
                ·
                  refine ⟨7417808173229500668230165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19780821795278668448613773 7417808173229500668230165)
                  ·
                    refine ⟨347709758120132843823289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7417808173229500668230165 347709758120132843823289)
                    ·
                      rfl

theorem cell23_2031487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_2031487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031487 prefixEnd_2031487 := by exact prefixLift 2031487
  have htrace : WordTrace (prefixWord ++ tailWord_2031487) baseStart_2031487 baseEnd_2031487 := by
    simpa [prefixWord, tailWord_2031487, baseEnd_2031487] using wordTrace_append hprefix tailTrace_2031487
  have hstable : (prefixWord ++ tailWord_2031487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031487).length < 2 ^ (prefixWord ++ tailWord_2031487).sum := by decide
  have hdescent : baseEnd_2031487 < baseStart_2031487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031524 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2031524 : Nat := 118140960795 + 2031524 * 2 ^ 59
def prefixEnd_2031524 : Nat := 4983230072969 + 3 ^ 40 * 2031524 * 2
def baseEnd_2031524 : Nat := 1043148273144614886707197

theorem tailTrace_2031524 : CollatzResearch.WordTrace tailWord_2031524 prefixEnd_2031524 1043148273144614886707197 := by
  unfold tailWord_2031524
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047883746071489760838813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49397178328095319681118417 37047883746071489760838813)
  ·
    refine ⟨13892956404776808660314555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37047883746071489760838813 13892956404776808660314555)
    ·
      refine ⟨20839434607165212990471833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892956404776808660314555 20839434607165212990471833)
      ·
        refine ⟨15629575955373909742853875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20839434607165212990471833 15629575955373909742853875)
        ·
          refine ⟨23444363933060864614280813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15629575955373909742853875 23444363933060864614280813)
          ·
            refine ⟨8791636474897824230355305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23444363933060864614280813 8791636474897824230355305)
            ·
              refine ⟨6593727356173368172766479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791636474897824230355305 6593727356173368172766479)
              ·
                refine ⟨9890591034260052259149719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593727356173368172766479 9890591034260052259149719)
                ·
                  refine ⟨14835886551390078388724579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890591034260052259149719 14835886551390078388724579)
                  ·
                    refine ⟨22253829827085117583086869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14835886551390078388724579 22253829827085117583086869)
                    ·
                      refine ⟨1043148273144614886707197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22253829827085117583086869 1043148273144614886707197)
                      ·
                        rfl

theorem cell23_2031524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2031524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031524 prefixEnd_2031524 := by exact prefixLift 2031524
  have htrace : WordTrace (prefixWord ++ tailWord_2031524) baseStart_2031524 baseEnd_2031524 := by
    simpa [prefixWord, tailWord_2031524, baseEnd_2031524] using wordTrace_append hprefix tailTrace_2031524
  have hstable : (prefixWord ++ tailWord_2031524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031524).length < 2 ^ (prefixWord ++ tailWord_2031524).sum := by decide
  have hdescent : baseEnd_2031524 < baseStart_2031524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031541 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2031541 : Nat := 118140960795 + 2031541 * 2 ^ 59
def prefixEnd_2031541 : Nat := 4983230072969 + 3 ^ 40 * 2031541 * 2
def baseEnd_2031541 : Nat := 1043157002315741320194619

theorem tailTrace_2031541 : CollatzResearch.WordTrace tailWord_2031541 prefixEnd_2031541 1043157002315741320194619 := by
  unfold tailWord_2031541
  simp only [CollatzResearch.WordTrace]
  refine ⟨74096387533081391425046477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49397591688720927616697651 74096387533081391425046477)
  ·
    refine ⟨27786145324905521784392429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74096387533081391425046477 27786145324905521784392429)
    ·
      refine ⟨10419804496839570669147161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27786145324905521784392429 10419804496839570669147161)
      ·
        refine ⟨7814853372629678001860371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10419804496839570669147161 7814853372629678001860371)
        ·
          refine ⟨11722280058944517002790557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814853372629678001860371 11722280058944517002790557)
          ·
            refine ⟨4395855022104193876046459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11722280058944517002790557 4395855022104193876046459)
            ·
              refine ⟨6593782533156290814069689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395855022104193876046459 6593782533156290814069689)
              ·
                refine ⟨4945336899867218110552267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6593782533156290814069689 4945336899867218110552267)
                ·
                  refine ⟨7418005349800827165828401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945336899867218110552267 7418005349800827165828401)
                  ·
                    refine ⟨5563504012350620374371301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7418005349800827165828401 5563504012350620374371301)
                    ·
                      refine ⟨1043157002315741320194619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5563504012350620374371301 1043157002315741320194619)
                      ·
                        rfl

theorem cell23_2031541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2031541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031541 prefixEnd_2031541 := by exact prefixLift 2031541
  have htrace : WordTrace (prefixWord ++ tailWord_2031541) baseStart_2031541 baseEnd_2031541 := by
    simpa [prefixWord, tailWord_2031541, baseEnd_2031541] using wordTrace_append hprefix tailTrace_2031541
  have hstable : (prefixWord ++ tailWord_2031541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031541).length < 2 ^ (prefixWord ++ tailWord_2031541).sum := by decide
  have hdescent : baseEnd_2031541 < baseStart_2031541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031545 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2031545 : Nat := 118140960795 + 2031545 * 2 ^ 59
def prefixEnd_2031545 : Nat := 4983230072969 + 3 ^ 40 * 2031545 * 2
def baseEnd_2031545 : Nat := 1043159056238359304544601

theorem tailTrace_2031545 : CollatzResearch.WordTrace tailWord_2031545 prefixEnd_2031545 1043159056238359304544601 := by
  unfold tailWord_2031545
  simp only [CollatzResearch.WordTrace]
  refine ⟨74096533425066900108192089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49397688950044600072128059 74096533425066900108192089)
  ·
    refine ⟨55572400068800175081144067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74096533425066900108192089 55572400068800175081144067)
    ·
      refine ⟨83358600103200262621716101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55572400068800175081144067 83358600103200262621716101)
      ·
        refine ⟨15629737519350049241571769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83358600103200262621716101 15629737519350049241571769)
        ·
          refine ⟨11722303139512536931178827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15629737519350049241571769 11722303139512536931178827)
          ·
            refine ⟨17583454709268805396768241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722303139512536931178827 17583454709268805396768241)
            ·
              refine ⟨13187591031951604047576181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17583454709268805396768241 13187591031951604047576181)
              ·
                refine ⟨1236336659245462879460267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13187591031951604047576181 1236336659245462879460267)
                ·
                  refine ⟨1854504988868194319190401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236336659245462879460267 1854504988868194319190401)
                  ·
                    refine ⟨1390878741651145739392801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1854504988868194319190401 1390878741651145739392801)
                    ·
                      refine ⟨1043159056238359304544601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390878741651145739392801 1043159056238359304544601)
                      ·
                        rfl

theorem cell23_2031545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2031545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031545 prefixEnd_2031545 := by exact prefixLift 2031545
  have htrace : WordTrace (prefixWord ++ tailWord_2031545) baseStart_2031545 baseEnd_2031545 := by
    simpa [prefixWord, tailWord_2031545, baseEnd_2031545] using wordTrace_append hprefix tailTrace_2031545
  have hstable : (prefixWord ++ tailWord_2031545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031545).length < 2 ^ (prefixWord ++ tailWord_2031545).sum := by decide
  have hdescent : baseEnd_2031545 < baseStart_2031545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031547 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 9]
def baseStart_2031547 : Nat := 118140960795 + 2031547 * 2 ^ 59
def prefixEnd_2031547 : Nat := 4983230072969 + 3 ^ 40 * 2031547 * 2
def baseEnd_2031547 : Nat := 347720027733222765573197

theorem tailTrace_2031547 : CollatzResearch.WordTrace tailWord_2031547 prefixEnd_2031547 347720027733222765573197 := by
  unfold tailWord_2031547
  simp only [CollatzResearch.WordTrace]
  refine ⟨74096606371059654449764895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49397737580706436299843263 74096606371059654449764895)
  ·
    refine ⟨111144909556589481674647343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74096606371059654449764895 111144909556589481674647343)
    ·
      refine ⟨166717364334884222511971015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111144909556589481674647343 166717364334884222511971015)
      ·
        refine ⟨250076046502326333767956523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166717364334884222511971015 250076046502326333767956523)
        ·
          refine ⟨375114069753489500651934785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250076046502326333767956523 375114069753489500651934785)
          ·
            refine ⟨281335552315117125488951089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375114069753489500651934785 281335552315117125488951089)
            ·
              refine ⟨211001664236337844116713317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281335552315117125488951089 211001664236337844116713317)
              ·
                refine ⟨39562812044313345771883747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211001664236337844116713317 39562812044313345771883747)
                ·
                  refine ⟨59344218066470018657825621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39562812044313345771883747 59344218066470018657825621)
                  ·
                    refine ⟨347720027733222765573197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59344218066470018657825621 347720027733222765573197)
                    ·
                      rfl

theorem cell23_2031547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_2031547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031547 prefixEnd_2031547 := by exact prefixLift 2031547
  have htrace : WordTrace (prefixWord ++ tailWord_2031547) baseStart_2031547 baseEnd_2031547 := by
    simpa [prefixWord, tailWord_2031547, baseEnd_2031547] using wordTrace_append hprefix tailTrace_2031547
  have hstable : (prefixWord ++ tailWord_2031547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031547).length < 2 ^ (prefixWord ++ tailWord_2031547).sum := by decide
  have hdescent : baseEnd_2031547 < baseStart_2031547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031562 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_2031562 : Nat := 118140960795 + 2031562 * 2 ^ 59
def prefixEnd_2031562 : Nat := 4983230072969 + 3 ^ 40 * 2031562 * 2
def baseEnd_2031562 : Nat := 1043167785409485738032023

theorem tailTrace_2031562 : CollatzResearch.WordTrace tailWord_2031562 prefixEnd_2031562 1043167785409485738032023 := by
  unfold tailWord_2031562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524288366501328002890235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49398102310670208007707293 18524288366501328002890235)
  ·
    refine ⟨27786432549751992004335353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524288366501328002890235 27786432549751992004335353)
    ·
      refine ⟨20839824412313994003251515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27786432549751992004335353 20839824412313994003251515)
      ·
        refine ⟨31259736618470991004877273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20839824412313994003251515 31259736618470991004877273)
        ·
          refine ⟨23444802463853243253657955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31259736618470991004877273 23444802463853243253657955)
          ·
            refine ⟨35167203695779864880486933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23444802463853243253657955 35167203695779864880486933)
            ·
              refine ⟨1648462673239681166272825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35167203695779864880486933 1648462673239681166272825)
              ·
                refine ⟨1236347004929760874704619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648462673239681166272825 1236347004929760874704619)
                ·
                  refine ⟨1854520507394641312056929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236347004929760874704619 1854520507394641312056929)
                  ·
                    refine ⟨1390890380545980984042697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1854520507394641312056929 1390890380545980984042697)
                    ·
                      refine ⟨1043167785409485738032023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390890380545980984042697 1043167785409485738032023)
                      ·
                        rfl

theorem cell23_2031562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_2031562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031562 prefixEnd_2031562 := by exact prefixLift 2031562
  have htrace : WordTrace (prefixWord ++ tailWord_2031562) baseStart_2031562 baseEnd_2031562 := by
    simpa [prefixWord, tailWord_2031562, baseEnd_2031562] using wordTrace_append hprefix tailTrace_2031562
  have hstable : (prefixWord ++ tailWord_2031562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031562).length < 2 ^ (prefixWord ++ tailWord_2031562).sum := by decide
  have hdescent : baseEnd_2031562 < baseStart_2031562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031564 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_2031564 : Nat := 118140960795 + 2031564 * 2 ^ 59
def prefixEnd_2031564 : Nat := 4983230072969 + 3 ^ 40 * 2031564 * 2
def baseEnd_2031564 : Nat := 347722937456931576735671

theorem tailTrace_2031564 : CollatzResearch.WordTrace tailWord_2031564 prefixEnd_2031564 347722937456931576735671 := by
  unfold tailWord_2031564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37048613205999033176566873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49398150941332044235422497 37048613205999033176566873)
  ·
    refine ⟨27786459904499274882425155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37048613205999033176566873 27786459904499274882425155)
    ·
      refine ⟨41679689856748912323637733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27786459904499274882425155 41679689856748912323637733)
      ·
        refine ⟨7814941848140421060682075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41679689856748912323637733 7814941848140421060682075)
        ·
          refine ⟨11722412772210631591023113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814941848140421060682075 11722412772210631591023113)
          ·
            refine ⟨8791809579157973693267335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11722412772210631591023113 8791809579157973693267335)
            ·
              refine ⟨13187714368736960539901003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8791809579157973693267335 13187714368736960539901003)
              ·
                refine ⟨19781571553105440809851505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13187714368736960539901003 19781571553105440809851505)
                ·
                  refine ⟨14836178664829080607388629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19781571553105440809851505 14836178664829080607388629)
                  ·
                    refine ⟨347722937456931576735671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14836178664829080607388629 347722937456931576735671)
                    ·
                      rfl

theorem cell23_2031564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_2031564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031564 prefixEnd_2031564 := by exact prefixLift 2031564
  have htrace : WordTrace (prefixWord ++ tailWord_2031564) baseStart_2031564 baseEnd_2031564 := by
    simpa [prefixWord, tailWord_2031564, baseEnd_2031564] using wordTrace_append hprefix tailTrace_2031564
  have hstable : (prefixWord ++ tailWord_2031564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031564).length < 2 ^ (prefixWord ++ tailWord_2031564).sum := by decide
  have hdescent : baseEnd_2031564 < baseStart_2031564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031578 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_2031578 : Nat := 118140960795 + 2031578 * 2 ^ 59
def prefixEnd_2031578 : Nat := 4983230072969 + 3 ^ 40 * 2031578 * 2
def baseEnd_2031578 : Nat := 1043176001099957675431949

theorem tailTrace_2031578 : CollatzResearch.WordTrace tailWord_2031578 prefixEnd_2031578 1043176001099957675431949 := by
  unfold tailWord_2031578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524434258486836686035847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49398491355964897829428925 18524434258486836686035847)
  ·
    refine ⟨27786651387730255029053771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524434258486836686035847 27786651387730255029053771)
    ·
      refine ⟨41679977081595382543580657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27786651387730255029053771 41679977081595382543580657)
      ·
        refine ⟨31259982811196536907685493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41679977081595382543580657 31259982811196536907685493)
        ·
          refine ⟨2930623388549675335095515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31259982811196536907685493 2930623388549675335095515)
          ·
            refine ⟨4395935082824513002643273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930623388549675335095515 4395935082824513002643273)
            ·
              refine ⟨3296951312118384751982455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4395935082824513002643273 3296951312118384751982455)
              ·
                refine ⟨4945426968177577127973683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296951312118384751982455 4945426968177577127973683)
                ·
                  refine ⟨7418140452266365691960525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945426968177577127973683 7418140452266365691960525)
                  ·
                    refine ⟨2781802669599887134485197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7418140452266365691960525 2781802669599887134485197)
                    ·
                      refine ⟨1043176001099957675431949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2781802669599887134485197 1043176001099957675431949)
                      ·
                        rfl

theorem cell23_2031578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_2031578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031578 prefixEnd_2031578 := by exact prefixLift 2031578
  have htrace : WordTrace (prefixWord ++ tailWord_2031578) baseStart_2031578 baseEnd_2031578 := by
    simpa [prefixWord, tailWord_2031578, baseEnd_2031578] using wordTrace_append hprefix tailTrace_2031578
  have hstable : (prefixWord ++ tailWord_2031578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031578).length < 2 ^ (prefixWord ++ tailWord_2031578).sum := by decide
  have hdescent : baseEnd_2031578 < baseStart_2031578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031588 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_2031588 : Nat := 118140960795 + 2031588 * 2 ^ 59
def prefixEnd_2031588 : Nat := 4983230072969 + 3 ^ 40 * 2031588 * 2
def baseEnd_2031588 : Nat := 1043181135906502636306903

theorem tailTrace_2031588 : CollatzResearch.WordTrace tailWord_2031588 prefixEnd_2031588 1043181135906502636306903 := by
  unfold tailWord_2031588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049050881955559226003709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49398734509274078968004945 37049050881955559226003709)
  ·
    refine ⟨13893394080733334709751391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37049050881955559226003709 13893394080733334709751391)
    ·
      refine ⟨20840091121100002064627087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13893394080733334709751391 20840091121100002064627087)
      ·
        refine ⟨31260136681650003096940631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20840091121100002064627087 31260136681650003096940631)
        ·
          refine ⟨46890205022475004645410947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31260136681650003096940631 46890205022475004645410947)
          ·
            refine ⟨70335307533712506968116421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46890205022475004645410947 70335307533712506968116421)
            ·
              refine ⟨13187870162571095056521829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70335307533712506968116421 13187870162571095056521829)
              ·
                refine ⟨2472725655482080323097843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13187870162571095056521829 2472725655482080323097843)
                ·
                  refine ⟨3709088483223120484646765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472725655482080323097843 3709088483223120484646765)
                  ·
                    refine ⟨1390908181208670181742537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709088483223120484646765 1390908181208670181742537)
                    ·
                      refine ⟨1043181135906502636306903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1390908181208670181742537 1043181135906502636306903)
                      ·
                        rfl

theorem cell23_2031588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_2031588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031588 prefixEnd_2031588 := by exact prefixLift 2031588
  have htrace : WordTrace (prefixWord ++ tailWord_2031588) baseStart_2031588 baseEnd_2031588 := by
    simpa [prefixWord, tailWord_2031588, baseEnd_2031588] using wordTrace_append hprefix tailTrace_2031588
  have hstable : (prefixWord ++ tailWord_2031588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031588).length < 2 ^ (prefixWord ++ tailWord_2031588).sum := by decide
  have hdescent : baseEnd_2031588 < baseStart_2031588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031594 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2031594 : Nat := 118140960795 + 2031594 * 2 ^ 59
def prefixEnd_2031594 : Nat := 4983230072969 + 3 ^ 40 * 2031594 * 2
def baseEnd_2031594 : Nat := 347728072263476537610625

theorem tailTrace_2031594 : CollatzResearch.WordTrace tailWord_2031594 prefixEnd_2031594 347728072263476537610625 := by
  unfold tailWord_2031594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524580150472345369181459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49398880401259587651150557 18524580150472345369181459)
  ·
    refine ⟨27786870225708518053772189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524580150472345369181459 27786870225708518053772189)
    ·
      refine ⟨10420076334640694270164571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27786870225708518053772189 10420076334640694270164571)
      ·
        refine ⟨15630114501961041405246857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420076334640694270164571 15630114501961041405246857)
        ·
          refine ⟨11722585876470781053935143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15630114501961041405246857 11722585876470781053935143)
          ·
            refine ⟨17583878814706171580902715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722585876470781053935143 17583878814706171580902715)
            ·
              refine ⟨26375818222059257371354073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583878814706171580902715 26375818222059257371354073)
              ·
                refine ⟨19781863666544443028515555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26375818222059257371354073 19781863666544443028515555)
                ·
                  refine ⟨29672795499816664542773333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19781863666544443028515555 29672795499816664542773333)
                  ·
                    refine ⟨347728072263476537610625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29672795499816664542773333 347728072263476537610625)
                    ·
                      rfl

theorem cell23_2031594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2031594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031594 prefixEnd_2031594 := by exact prefixLift 2031594
  have htrace : WordTrace (prefixWord ++ tailWord_2031594) baseStart_2031594 baseEnd_2031594 := by
    simpa [prefixWord, tailWord_2031594, baseEnd_2031594] using wordTrace_append hprefix tailTrace_2031594
  have hstable : (prefixWord ++ tailWord_2031594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031594).length < 2 ^ (prefixWord ++ tailWord_2031594).sum := by decide
  have hdescent : baseEnd_2031594 < baseStart_2031594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031629 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2031629 : Nat := 118140960795 + 2031629 * 2 ^ 59
def prefixEnd_2031629 : Nat := 4983230072969 + 3 ^ 40 * 2031629 * 2
def baseEnd_2031629 : Nat := 1043202188613336975894215

theorem tailTrace_2031629 : CollatzResearch.WordTrace tailWord_2031629 prefixEnd_2031629 1043202188613336975894215 := by
  unfold tailWord_2031629
  simp only [CollatzResearch.WordTrace]
  refine ⟨74099597156762582454249941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49399731437841721636166627 74099597156762582454249941)
  ·
    refine ⟨1736709308361623026271483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74099597156762582454249941 1736709308361623026271483)
    ·
      refine ⟨2605063962542434539407225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1736709308361623026271483 2605063962542434539407225)
      ·
        refine ⟨1953797971906825904555419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2605063962542434539407225 1953797971906825904555419)
        ·
          refine ⟨2930696957860238856833129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1953797971906825904555419 2930696957860238856833129)
          ·
            refine ⟨2198022718395179142624847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2930696957860238856833129 2198022718395179142624847)
            ·
              refine ⟨3297034077592768713937271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198022718395179142624847 3297034077592768713937271)
              ·
                refine ⟨4945551116389153070905907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297034077592768713937271 4945551116389153070905907)
                ·
                  refine ⟨7418326674583729606358861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945551116389153070905907 7418326674583729606358861)
                  ·
                    refine ⟨2781872502968898602384573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7418326674583729606358861 2781872502968898602384573)
                    ·
                      refine ⟨1043202188613336975894215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2781872502968898602384573 1043202188613336975894215)
                      ·
                        rfl

theorem cell23_2031629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2031629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031629 prefixEnd_2031629 := by exact prefixLift 2031629
  have htrace : WordTrace (prefixWord ++ tailWord_2031629) baseStart_2031629 baseEnd_2031629 := by
    simpa [prefixWord, tailWord_2031629, baseEnd_2031629] using wordTrace_append hprefix tailTrace_2031629
  have hstable : (prefixWord ++ tailWord_2031629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031629).length < 2 ^ (prefixWord ++ tailWord_2031629).sum := by decide
  have hdescent : baseEnd_2031629 < baseStart_2031629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031681 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2031681 : Nat := 118140960795 + 2031681 * 2 ^ 59
def prefixEnd_2031681 : Nat := 4983230072969 + 3 ^ 40 * 2031681 * 2
def baseEnd_2031681 : Nat := 1043228889607370772443975

theorem tailTrace_2031681 : CollatzResearch.WordTrace tailWord_2031681 prefixEnd_2031681 1043228889607370772443975 := by
  unfold tailWord_2031681
  simp only [CollatzResearch.WordTrace]
  refine ⟨74101493752574195335142897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49400995835049463556761931 74101493752574195335142897)
  ·
    refine ⟨55576120314430646501357173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74101493752574195335142897 55576120314430646501357173)
    ·
      refine ⟨5210261279477873109502235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55576120314430646501357173 5210261279477873109502235)
      ·
        refine ⟨7815391919216809664253353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210261279477873109502235 7815391919216809664253353)
        ·
          refine ⟨5861543939412607248190015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7815391919216809664253353 5861543939412607248190015)
          ·
            refine ⟨8792315909118910872285023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861543939412607248190015 8792315909118910872285023)
            ·
              refine ⟨13188473863678366308427535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792315909118910872285023 13188473863678366308427535)
              ·
                refine ⟨19782710795517549462641303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188473863678366308427535 19782710795517549462641303)
                ·
                  refine ⟨29674066193276324193961955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19782710795517549462641303 29674066193276324193961955)
                  ·
                    refine ⟨44511099289914486290942933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29674066193276324193961955 44511099289914486290942933)
                    ·
                      refine ⟨1043228889607370772443975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44511099289914486290942933 1043228889607370772443975)
                      ·
                        rfl

theorem cell23_2031681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2031681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031681 prefixEnd_2031681 := by exact prefixLift 2031681
  have htrace : WordTrace (prefixWord ++ tailWord_2031681) baseStart_2031681 baseEnd_2031681 := by
    simpa [prefixWord, tailWord_2031681, baseEnd_2031681] using wordTrace_append hprefix tailTrace_2031681
  have hstable : (prefixWord ++ tailWord_2031681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031681).length < 2 ^ (prefixWord ++ tailWord_2031681).sum := by decide
  have hdescent : baseEnd_2031681 < baseStart_2031681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031708 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2031708 : Nat := 118140960795 + 2031708 * 2 ^ 59
def prefixEnd_2031708 : Nat := 4983230072969 + 3 ^ 40 * 2031708 * 2
def baseEnd_2031708 : Nat := 1043242753585042166806351

theorem tailTrace_2031708 : CollatzResearch.WordTrace tailWord_2031708 prefixEnd_2031708 1043242753585042166806351 := by
  unfold tailWord_2031708
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051239261738189473187889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49401652348984252630917185 37051239261738189473187889)
  ·
    refine ⟨27788429446303642104890917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37051239261738189473187889 27788429446303642104890917)
    ·
      refine ⟨5210330521181932894667047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27788429446303642104890917 5210330521181932894667047)
      ·
        refine ⟨7815495781772899342000571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210330521181932894667047 7815495781772899342000571)
        ·
          refine ⟨11723243672659349013000857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815495781772899342000571 11723243672659349013000857)
          ·
            refine ⟨8792432754494511759750643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11723243672659349013000857 8792432754494511759750643)
            ·
              refine ⟨13188649131741767639625965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792432754494511759750643 13188649131741767639625965)
              ·
                refine ⟨4945743424403162864859737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13188649131741767639625965 4945743424403162864859737)
                ·
                  refine ⟨3709307568302372148644803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945743424403162864859737 3709307568302372148644803)
                  ·
                    refine ⟨5563961352453558222967205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709307568302372148644803 5563961352453558222967205)
                    ·
                      refine ⟨1043242753585042166806351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5563961352453558222967205 1043242753585042166806351)
                      ·
                        rfl

theorem cell23_2031708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2031708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031708 prefixEnd_2031708 := by exact prefixLift 2031708
  have htrace : WordTrace (prefixWord ++ tailWord_2031708) baseStart_2031708 baseEnd_2031708 := by
    simpa [prefixWord, tailWord_2031708, baseEnd_2031708] using wordTrace_append hprefix tailTrace_2031708
  have hstable : (prefixWord ++ tailWord_2031708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031708).length < 2 ^ (prefixWord ++ tailWord_2031708).sum := by decide
  have hdescent : baseEnd_2031708 < baseStart_2031708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031728 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_2031728 : Nat := 118140960795 + 2031728 * 2 ^ 59
def prefixEnd_2031728 : Nat := 4983230072969 + 3 ^ 40 * 2031728 * 2
def baseEnd_2031728 : Nat := 1043253023198132088556259

theorem tailTrace_2031728 : CollatzResearch.WordTrace tailWord_2031728 prefixEnd_2031728 1043253023198132088556259 := by
  unfold tailWord_2031728
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051603991701961181051919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49402138655602614908069225 37051603991701961181051919)
  ·
    refine ⟨55577405987552941771577879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37051603991701961181051919 55577405987552941771577879)
    ·
      refine ⟨83366108981329412657366819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55577405987552941771577879 83366108981329412657366819)
      ·
        refine ⟨125049163471994118986050229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83366108981329412657366819 125049163471994118986050229)
        ·
          refine ⟨11723359075499448654942209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125049163471994118986050229 11723359075499448654942209)
          ·
            refine ⟨8792519306624586491206657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11723359075499448654942209 8792519306624586491206657)
            ·
              refine ⟨6594389479968439868404993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792519306624586491206657 6594389479968439868404993)
              ·
                refine ⟨4945792109976329901303745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594389479968439868404993 4945792109976329901303745)
                ·
                  refine ⟨3709344082482247425977809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945792109976329901303745 3709344082482247425977809)
                  ·
                    refine ⟨2782008061861685569483357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709344082482247425977809 2782008061861685569483357)
                    ·
                      refine ⟨1043253023198132088556259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2782008061861685569483357 1043253023198132088556259)
                      ·
                        rfl

theorem cell23_2031728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_2031728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031728 prefixEnd_2031728 := by exact prefixLift 2031728
  have htrace : WordTrace (prefixWord ++ tailWord_2031728) baseStart_2031728 baseEnd_2031728 := by
    simpa [prefixWord, tailWord_2031728, baseEnd_2031728] using wordTrace_append hprefix tailTrace_2031728
  have hstable : (prefixWord ++ tailWord_2031728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031728).length < 2 ^ (prefixWord ++ tailWord_2031728).sum := by decide
  have hdescent : baseEnd_2031728 < baseStart_2031728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031735 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 1, 4]
def baseStart_2031735 : Nat := 118140960795 + 2031735 * 2 ^ 59
def prefixEnd_2031735 : Nat := 4983230072969 + 3 ^ 40 * 2031735 * 2
def baseEnd_2031735 : Nat := 347752205854237853722909

theorem tailTrace_2031735 : CollatzResearch.WordTrace tailWord_2031735 prefixEnd_2031735 347752205854237853722909 := by
  unfold tailWord_2031735
  simp only [CollatzResearch.WordTrace]
  refine ⟨74103463294378562557608659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49402308862919041705072439 74103463294378562557608659)
  ·
    refine ⟨111155194941567843836412989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74103463294378562557608659 111155194941567843836412989)
    ·
      refine ⟨41683198103087941438654871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111155194941567843836412989 41683198103087941438654871)
      ·
        refine ⟨62524797154631912157982307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41683198103087941438654871 62524797154631912157982307)
        ·
          refine ⟨93787195731947868236973461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62524797154631912157982307 93787195731947868236973461)
          ·
            refine ⟨4396274799935056323608131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93787195731947868236973461 4396274799935056323608131)
            ·
              refine ⟨6594412199902584485412197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396274799935056323608131 6594412199902584485412197)
              ·
                refine ⟨1236452287481734591014787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6594412199902584485412197 1236452287481734591014787)
                ·
                  refine ⟨1854678431222601886522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236452287481734591014787 1854678431222601886522181)
                  ·
                    refine ⟨347752205854237853722909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1854678431222601886522181 347752205854237853722909)
                    ·
                      rfl

theorem cell23_2031735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_2031735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031735 prefixEnd_2031735 := by exact prefixLift 2031735
  have htrace : WordTrace (prefixWord ++ tailWord_2031735) baseStart_2031735 baseEnd_2031735 := by
    simpa [prefixWord, tailWord_2031735, baseEnd_2031735] using wordTrace_append hprefix tailTrace_2031735
  have hstable : (prefixWord ++ tailWord_2031735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031735).length < 2 ^ (prefixWord ++ tailWord_2031735).sum := by decide
  have hdescent : baseEnd_2031735 < baseStart_2031735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031808 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_2031808 : Nat := 118140960795 + 2031808 * 2 ^ 59
def prefixEnd_2031808 : Nat := 4983230072969 + 3 ^ 40 * 2031808 * 2
def baseEnd_2031808 : Nat := 347764700550163925185297

theorem tailTrace_2031808 : CollatzResearch.WordTrace tailWord_2031808 prefixEnd_2031808 347764700550163925185297 := by
  unfold tailWord_2031808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37053062911557048012508039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49404083882076064016677385 37053062911557048012508039)
  ·
    refine ⟨55579594367335572018762059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37053062911557048012508039 55579594367335572018762059)
    ·
      refine ⟨83369391551003358028143089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55579594367335572018762059 83369391551003358028143089)
      ·
        refine ⟨62527043663252518521107317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83369391551003358028143089 62527043663252518521107317)
        ·
          refine ⟨5861910343429923611353811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62527043663252518521107317 5861910343429923611353811)
          ·
            refine ⟨8792865515144885417030717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861910343429923611353811 8792865515144885417030717)
            ·
              refine ⟨3297324568179332031386519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8792865515144885417030717 3297324568179332031386519)
              ·
                refine ⟨4945986852268998047079779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297324568179332031386519 4945986852268998047079779)
                ·
                  refine ⟨7418980278403497070619669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945986852268998047079779 7418980278403497070619669)
                  ·
                    refine ⟨347764700550163925185297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7418980278403497070619669 347764700550163925185297)
                    ·
                      rfl

theorem cell23_2031808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_2031808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031808 prefixEnd_2031808 := by exact prefixLift 2031808
  have htrace : WordTrace (prefixWord ++ tailWord_2031808) baseStart_2031808 baseEnd_2031808 := by
    simpa [prefixWord, tailWord_2031808, baseEnd_2031808] using wordTrace_append hprefix tailTrace_2031808
  have hstable : (prefixWord ++ tailWord_2031808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031808).length < 2 ^ (prefixWord ++ tailWord_2031808).sum := by decide
  have hdescent : baseEnd_2031808 < baseStart_2031808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031851 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 7]
def baseStart_2031851 : Nat := 118140960795 + 2031851 * 2 ^ 59
def prefixEnd_2031851 : Nat := 4983230072969 + 3 ^ 40 * 2031851 * 2
def baseEnd_2031851 : Nat := 347772060439545035772731

theorem tailTrace_2031851 : CollatzResearch.WordTrace tailWord_2031851 prefixEnd_2031851 347772060439545035772731 := by
  unfold tailWord_2031851
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107694161958314368831407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49405129441305542912554271 74107694161958314368831407)
  ·
    refine ⟨111161541242937471553247111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74107694161958314368831407 111161541242937471553247111)
    ·
      refine ⟨166742311864406207329870667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111161541242937471553247111 166742311864406207329870667)
      ·
        refine ⟨250113467796609310994806001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166742311864406207329870667 250113467796609310994806001)
        ·
          refine ⟨187585100847456983246104501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250113467796609310994806001 187585100847456983246104501)
          ·
            refine ⟨17586103204449092179322297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187585100847456983246104501 17586103204449092179322297)
            ·
              refine ⟨13189577403336819134491723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17586103204449092179322297 13189577403336819134491723)
              ·
                refine ⟨19784366105005228701737585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13189577403336819134491723 19784366105005228701737585)
                ·
                  refine ⟨14838274578753921526303189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19784366105005228701737585 14838274578753921526303189)
                  ·
                    refine ⟨347772060439545035772731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14838274578753921526303189 347772060439545035772731)
                    ·
                      rfl

theorem cell23_2031851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_2031851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031851 prefixEnd_2031851 := by exact prefixLift 2031851
  have htrace : WordTrace (prefixWord ++ tailWord_2031851) baseStart_2031851 baseEnd_2031851 := by
    simpa [prefixWord, tailWord_2031851, baseEnd_2031851] using wordTrace_append hprefix tailTrace_2031851
  have hstable : (prefixWord ++ tailWord_2031851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031851).length < 2 ^ (prefixWord ++ tailWord_2031851).sum := by decide
  have hdescent : baseEnd_2031851 < baseStart_2031851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031875 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 3, 3, 2]
def baseStart_2031875 : Nat := 118140960795 + 2031875 * 2 ^ 59
def prefixEnd_2031875 : Nat := 4983230072969 + 3 ^ 40 * 2031875 * 2
def baseEnd_2031875 : Nat := 1043328504854343013418083

theorem tailTrace_2031875 : CollatzResearch.WordTrace tailWord_2031875 prefixEnd_2031875 1043328504854343013418083 := by
  unfold tailWord_2031875
  simp only [CollatzResearch.WordTrace]
  refine ⟨74108569513871366467705079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49405713009247577645136719 74108569513871366467705079)
  ·
    refine ⟨111162854270807049701557619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74108569513871366467705079 111162854270807049701557619)
    ·
      refine ⟨166744281406210574552336429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111162854270807049701557619 166744281406210574552336429)
      ·
        refine ⟨62529105527328965457126161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166744281406210574552336429 62529105527328965457126161)
        ·
          refine ⟨46896829145496724092844621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62529105527328965457126161 46896829145496724092844621)
          ·
            refine ⟨17586310929561271534816733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46896829145496724092844621 17586310929561271534816733)
            ·
              refine ⟨6594866598585476825556275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17586310929561271534816733 6594866598585476825556275)
              ·
                refine ⟨9892299897878215238334413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594866598585476825556275 9892299897878215238334413)
                ·
                  refine ⟨3709612461704330714375405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9892299897878215238334413 3709612461704330714375405)
                  ·
                    refine ⟨1391104673139124017890777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709612461704330714375405 1391104673139124017890777)
                    ·
                      refine ⟨1043328504854343013418083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391104673139124017890777 1043328504854343013418083)
                      ·
                        rfl

theorem cell23_2031875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_2031875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031875 prefixEnd_2031875 := by exact prefixLift 2031875
  have htrace : WordTrace (prefixWord ++ tailWord_2031875) baseStart_2031875 baseEnd_2031875 := by
    simpa [prefixWord, tailWord_2031875, baseEnd_2031875] using wordTrace_append hprefix tailTrace_2031875
  have hstable : (prefixWord ++ tailWord_2031875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031875).length < 2 ^ (prefixWord ++ tailWord_2031875).sum := by decide
  have hdescent : baseEnd_2031875 < baseStart_2031875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2031956 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_2031956 : Nat := 118140960795 + 2031956 * 2 ^ 59
def prefixEnd_2031956 : Nat := 4983230072969 + 3 ^ 40 * 2031956 * 2
def baseEnd_2031956 : Nat := 1043370096787357196505211

theorem tailTrace_2031956 : CollatzResearch.WordTrace tailWord_2031956 prefixEnd_2031956 1043370096787357196505211 := by
  unfold tailWord_2031956
  simp only [CollatzResearch.WordTrace]
  refine ⟨37055761913288958650701861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49407682551051944867602481 37055761913288958650701861)
  ·
    refine ⟨6947955358741679747006599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37055761913288958650701861 6947955358741679747006599)
    ·
      refine ⟨10421933038112519620509899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6947955358741679747006599 10421933038112519620509899)
      ·
        refine ⟨15632899557168779430764849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421933038112519620509899 15632899557168779430764849)
        ·
          refine ⟨11724674667876584573073637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15632899557168779430764849 11724674667876584573073637)
          ·
            refine ⟨2198376500226859607451307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11724674667876584573073637 2198376500226859607451307)
            ·
              refine ⟨3297564750340289411176961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198376500226859607451307 3297564750340289411176961)
              ·
                refine ⟨2473173562755217058382721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297564750340289411176961 2473173562755217058382721)
                ·
                  refine ⟨1854880172066412793787041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473173562755217058382721 1854880172066412793787041)
                  ·
                    refine ⟨1391160129049809595340281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1854880172066412793787041 1391160129049809595340281)
                    ·
                      refine ⟨1043370096787357196505211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391160129049809595340281 1043370096787357196505211)
                      ·
                        rfl

theorem cell23_2031956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_2031956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2031956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2031956 prefixEnd_2031956 := by exact prefixLift 2031956
  have htrace : WordTrace (prefixWord ++ tailWord_2031956) baseStart_2031956 baseEnd_2031956 := by
    simpa [prefixWord, tailWord_2031956, baseEnd_2031956] using wordTrace_append hprefix tailTrace_2031956
  have hstable : (prefixWord ++ tailWord_2031956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2031956).length < 2 ^ (prefixWord ++ tailWord_2031956).sum := by decide
  have hdescent : baseEnd_2031956 < baseStart_2031956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2031956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032035 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 6]
def baseStart_2032035 : Nat := 118140960795 + 2032035 * 2 ^ 59
def prefixEnd_2032035 : Nat := 4983230072969 + 3 ^ 40 * 2032035 * 2
def baseEnd_2032035 : Nat := 115934517973229154157483

theorem tailTrace_2032035 : CollatzResearch.WordTrace tailWord_2032035 prefixEnd_2032035 115934517973229154157483 := by
  unfold tailWord_2032035
  simp only [CollatzResearch.WordTrace]
  refine ⟨74114405193291713793529559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49409603462194475862353039 74114405193291713793529559)
  ·
    refine ⟨111171607789937570690294339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74114405193291713793529559 111171607789937570690294339)
    ·
      refine ⟨166757411684906356035441509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111171607789937570690294339 166757411684906356035441509)
      ·
        refine ⟨31267014690919941756645283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166757411684906356035441509 31267014690919941756645283)
        ·
          refine ⟨46900522036379912634967925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31267014690919941756645283 46900522036379912634967925)
          ·
            refine ⟨4396923940910616809528243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46900522036379912634967925 4396923940910616809528243)
            ·
              refine ⟨6595385911365925214292365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396923940910616809528243 6595385911365925214292365)
              ·
                refine ⟨2473269716762221955359637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6595385911365925214292365 2473269716762221955359637)
                ·
                  refine ⟨115934517973229154157483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2473269716762221955359637 115934517973229154157483)
                  ·
                    rfl

theorem cell23_2032035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 6].length) (baseStart_2032035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032035 prefixEnd_2032035 := by exact prefixLift 2032035
  have htrace : WordTrace (prefixWord ++ tailWord_2032035) baseStart_2032035 baseEnd_2032035 := by
    simpa [prefixWord, tailWord_2032035, baseEnd_2032035] using wordTrace_append hprefix tailTrace_2032035
  have hstable : (prefixWord ++ tailWord_2032035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032035).length < 2 ^ (prefixWord ++ tailWord_2032035).sum := by decide
  have hdescent : baseEnd_2032035 < baseStart_2032035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032058 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_2032058 : Nat := 118140960795 + 2032058 * 2 ^ 59
def prefixEnd_2032058 : Nat := 4983230072969 + 3 ^ 40 * 2032058 * 2
def baseEnd_2032058 : Nat := 1043422471814115797429741

theorem tailTrace_2032058 : CollatzResearch.WordTrace tailWord_2032058 prefixEnd_2032058 1043422471814115797429741 := by
  unfold tailWord_2032058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528811018052097180404207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49410162714805592481077885 18528811018052097180404207)
  ·
    refine ⟨27793216527078145770606311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18528811018052097180404207 27793216527078145770606311)
    ·
      refine ⟨41689824790617218655909467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27793216527078145770606311 41689824790617218655909467)
      ·
        refine ⟨62534737185925827983864201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41689824790617218655909467 62534737185925827983864201)
        ·
          refine ⟨46901052889444370987898151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62534737185925827983864201 46901052889444370987898151)
          ·
            refine ⟨70351579334166556481847227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46901052889444370987898151 70351579334166556481847227)
            ·
              refine ⟨105527369001249834722770841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70351579334166556481847227 105527369001249834722770841)
              ·
                refine ⟨79145526750937376042078131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105527369001249834722770841 79145526750937376042078131)
                ·
                  refine ⟨118718290126406064063117197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79145526750937376042078131 118718290126406064063117197)
                  ·
                    refine ⟨44519358797402274023668949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118718290126406064063117197 44519358797402274023668949)
                    ·
                      refine ⟨1043422471814115797429741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44519358797402274023668949 1043422471814115797429741)
                      ·
                        rfl

theorem cell23_2032058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_2032058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032058 prefixEnd_2032058 := by exact prefixLift 2032058
  have htrace : WordTrace (prefixWord ++ tailWord_2032058) baseStart_2032058 baseEnd_2032058 := by
    simpa [prefixWord, tailWord_2032058, baseEnd_2032058] using wordTrace_append hprefix tailTrace_2032058
  have hstable : (prefixWord ++ tailWord_2032058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032058).length < 2 ^ (prefixWord ++ tailWord_2032058).sum := by decide
  have hdescent : baseEnd_2032058 < baseStart_2032058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032095 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 1, 6]
def baseStart_2032095 : Nat := 118140960795 + 2032095 * 2 ^ 59
def prefixEnd_2032095 : Nat := 4983230072969 + 3 ^ 40 * 2032095 * 2
def baseEnd_2032095 : Nat := 347813823532777384222357

theorem tailTrace_2032095 : CollatzResearch.WordTrace tailWord_2032095 prefixEnd_2032095 347813823532777384222357 := by
  unfold tailWord_2032095
  simp only [CollatzResearch.WordTrace]
  refine ⟨74116593573074344040713739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49411062382049562693809159 74116593573074344040713739)
  ·
    refine ⟨111174890359611516061070609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74116593573074344040713739 111174890359611516061070609)
    ·
      refine ⟨83381167769708637045802957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111174890359611516061070609 83381167769708637045802957)
      ·
        refine ⟨31267937913640738892176109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83381167769708637045802957 31267937913640738892176109)
        ·
          refine ⟨11725476717615277084566041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31267937913640738892176109 11725476717615277084566041)
          ·
            refine ⟨8794107538211457813424531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725476717615277084566041 8794107538211457813424531)
            ·
              refine ⟨13191161307317186720136797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794107538211457813424531 13191161307317186720136797)
              ·
                refine ⟨4946685490243945020051299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13191161307317186720136797 4946685490243945020051299)
                ·
                  refine ⟨7420028235365917530076949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946685490243945020051299 7420028235365917530076949)
                  ·
                    refine ⟨347813823532777384222357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7420028235365917530076949 347813823532777384222357)
                    ·
                      rfl

theorem cell23_2032095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_2032095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032095 prefixEnd_2032095 := by exact prefixLift 2032095
  have htrace : WordTrace (prefixWord ++ tailWord_2032095) baseStart_2032095 baseEnd_2032095 := by
    simpa [prefixWord, tailWord_2032095, baseEnd_2032095] using wordTrace_append hprefix tailTrace_2032095
  have hstable : (prefixWord ++ tailWord_2032095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032095).length < 2 ^ (prefixWord ++ tailWord_2032095).sum := by decide
  have hdescent : baseEnd_2032095 < baseStart_2032095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032106 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_2032106 : Nat := 118140960795 + 2032106 * 2 ^ 59
def prefixEnd_2032106 : Nat := 4983230072969 + 3 ^ 40 * 2032106 * 2
def baseEnd_2032106 : Nat := 1043447118885531609629521

theorem tailTrace_2032106 : CollatzResearch.WordTrace tailWord_2032106 prefixEnd_2032106 1043447118885531609629521 := by
  unfold tailWord_2032106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18529248694008623229841043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49411329850689661946242781 18529248694008623229841043)
  ·
    refine ⟨27793873041012934844761565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18529248694008623229841043 27793873041012934844761565)
    ·
      refine ⟨10422702390379850566785587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27793873041012934844761565 10422702390379850566785587)
      ·
        refine ⟨15634053585569775850178381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422702390379850566785587 15634053585569775850178381)
        ·
          refine ⟨5862770094588665943816893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15634053585569775850178381 5862770094588665943816893)
          ·
            refine ⟨2198538785470749728931335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5862770094588665943816893 2198538785470749728931335)
            ·
              refine ⟨3297808178206124593397003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198538785470749728931335 3297808178206124593397003)
              ·
                refine ⟨4946712267309186890095505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297808178206124593397003 4946712267309186890095505)
                ·
                  refine ⟨3710034200481890167571629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946712267309186890095505 3710034200481890167571629)
                  ·
                    refine ⟨1391262825180708812839361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710034200481890167571629 1391262825180708812839361)
                    ·
                      refine ⟨1043447118885531609629521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391262825180708812839361 1043447118885531609629521)
                      ·
                        rfl

theorem cell23_2032106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_2032106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032106 prefixEnd_2032106 := by exact prefixLift 2032106
  have htrace : WordTrace (prefixWord ++ tailWord_2032106) baseStart_2032106 baseEnd_2032106 := by
    simpa [prefixWord, tailWord_2032106, baseEnd_2032106] using wordTrace_append hprefix tailTrace_2032106
  have hstable : (prefixWord ++ tailWord_2032106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032106).length < 2 ^ (prefixWord ++ tailWord_2032106).sum := by decide
  have hdescent : baseEnd_2032106 < baseStart_2032106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032115 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4]
def baseStart_2032115 : Nat := 118140960795 + 2032115 * 2 ^ 59
def prefixEnd_2032115 : Nat := 4983230072969 + 3 ^ 40 * 2032115 * 2
def baseEnd_2032115 : Nat := 1043451740211422074416979

theorem tailTrace_2032115 : CollatzResearch.WordTrace tailWord_2032115 prefixEnd_2032115 1043451740211422074416979 := by
  unfold tailWord_2032115
  simp only [CollatzResearch.WordTrace]
  refine ⟨74117323033001887456441799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49411548688667924970961199 74117323033001887456441799)
  ·
    refine ⟨111175984549502831184662699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74117323033001887456441799 111175984549502831184662699)
    ·
      refine ⟨166763976824254246776994049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111175984549502831184662699 166763976824254246776994049)
      ·
        refine ⟨125072982618190685082745537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166763976824254246776994049 125072982618190685082745537)
        ·
          refine ⟨93804736963643013812059153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125072982618190685082745537 93804736963643013812059153)
          ·
            refine ⟨70353552722732260359044365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93804736963643013812059153 70353552722732260359044365)
            ·
              refine ⟨26382582271024597634641637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70353552722732260359044365 26382582271024597634641637)
              ·
                refine ⟨4946734175817112056495307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26382582271024597634641637 4946734175817112056495307)
                ·
                  refine ⟨7420101263725668084742961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946734175817112056495307 7420101263725668084742961)
                  ·
                    refine ⟨5565075947794251063557221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420101263725668084742961 5565075947794251063557221)
                    ·
                      refine ⟨1043451740211422074416979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5565075947794251063557221 1043451740211422074416979)
                      ·
                        rfl

theorem cell23_2032115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_2032115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032115 prefixEnd_2032115 := by exact prefixLift 2032115
  have htrace : WordTrace (prefixWord ++ tailWord_2032115) baseStart_2032115 baseEnd_2032115 := by
    simpa [prefixWord, tailWord_2032115, baseEnd_2032115] using wordTrace_append hprefix tailTrace_2032115
  have hstable : (prefixWord ++ tailWord_2032115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032115).length < 2 ^ (prefixWord ++ tailWord_2032115).sum := by decide
  have hdescent : baseEnd_2032115 < baseStart_2032115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032129 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2032129 : Nat := 118140960795 + 2032129 * 2 ^ 59
def prefixEnd_2032129 : Nat := 4983230072969 + 3 ^ 40 * 2032129 * 2
def baseEnd_2032129 : Nat := 347819642980195006547305

theorem tailTrace_2032129 : CollatzResearch.WordTrace tailWord_2032129 prefixEnd_2032129 347819642980195006547305 := by
  unfold tailWord_2032129
  simp only [CollatzResearch.WordTrace]
  refine ⟨74117833654951167847451441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49411889103300778564967627 74117833654951167847451441)
  ·
    refine ⟨55588375241213375885588581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74117833654951167847451441 55588375241213375885588581)
    ·
      refine ⟨10422820357727507978547859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55588375241213375885588581 10422820357727507978547859)
      ·
        refine ⟨15634230536591261967821789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422820357727507978547859 15634230536591261967821789)
        ·
          refine ⟨5862836451221723237933171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15634230536591261967821789 5862836451221723237933171)
          ·
            refine ⟨8794254676832584856899757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862836451221723237933171 8794254676832584856899757)
            ·
              refine ⟨3297845503812219321337409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8794254676832584856899757 3297845503812219321337409)
              ·
                refine ⟨2473384127859164491003057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297845503812219321337409 2473384127859164491003057)
                ·
                  refine ⟨1855038095894373368252293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473384127859164491003057 1855038095894373368252293)
                  ·
                    refine ⟨347819642980195006547305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855038095894373368252293 347819642980195006547305)
                    ·
                      rfl

theorem cell23_2032129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2032129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032129 prefixEnd_2032129 := by exact prefixLift 2032129
  have htrace : WordTrace (prefixWord ++ tailWord_2032129) baseStart_2032129 baseEnd_2032129 := by
    simpa [prefixWord, tailWord_2032129, baseEnd_2032129] using wordTrace_append hprefix tailTrace_2032129
  have hstable : (prefixWord ++ tailWord_2032129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032129).length < 2 ^ (prefixWord ++ tailWord_2032129).sum := by decide
  have hdescent : baseEnd_2032129 < baseStart_2032129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032165 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_2032165 : Nat := 118140960795 + 2032165 * 2 ^ 59
def prefixEnd_2032165 : Nat := 4983230072969 + 3 ^ 40 * 2032165 * 2
def baseEnd_2032165 : Nat := 1043477414244146878791749

theorem tailTrace_2032165 : CollatzResearch.WordTrace tailWord_2032165 prefixEnd_2032165 1043477414244146878791749 := by
  unfold tailWord_2032165
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119146682820745995761949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49412764455213830663841299 74119146682820745995761949)
  ·
    refine ⟨27794680006057779748410731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74119146682820745995761949 27794680006057779748410731)
    ·
      refine ⟨41692020009086669622616097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27794680006057779748410731 41692020009086669622616097)
      ·
        refine ⟨31269015006815002216962073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41692020009086669622616097 31269015006815002216962073)
        ·
          refine ⟨23451761255111251662721555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31269015006815002216962073 23451761255111251662721555)
          ·
            refine ⟨35177641882666877494082333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23451761255111251662721555 35177641882666877494082333)
            ·
              refine ⟨13191615706000079060280875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35177641882666877494082333 13191615706000079060280875)
              ·
                refine ⟨19787423559000118590421313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191615706000079060280875 19787423559000118590421313)
                ·
                  refine ⟨14840567669250088942815985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19787423559000118590421313 14840567669250088942815985)
                  ·
                    refine ⟨11130425751937566707111989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14840567669250088942815985 11130425751937566707111989)
                    ·
                      refine ⟨1043477414244146878791749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11130425751937566707111989 1043477414244146878791749)
                      ·
                        rfl

theorem cell23_2032165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_2032165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032165 prefixEnd_2032165 := by exact prefixLift 2032165
  have htrace : WordTrace (prefixWord ++ tailWord_2032165) baseStart_2032165 baseEnd_2032165 := by
    simpa [prefixWord, tailWord_2032165, baseEnd_2032165] using wordTrace_append hprefix tailTrace_2032165
  have hstable : (prefixWord ++ tailWord_2032165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032165).length < 2 ^ (prefixWord ++ tailWord_2032165).sum := by decide
  have hdescent : baseEnd_2032165 < baseStart_2032165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032170 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_2032170 : Nat := 118140960795 + 2032170 * 2 ^ 59
def prefixEnd_2032170 : Nat := 4983230072969 + 3 ^ 40 * 2032170 * 2
def baseEnd_2032170 : Nat := 1043479981647419359229227

theorem tailTrace_2032170 : CollatzResearch.WordTrace tailWord_2032170 prefixEnd_2032170 1043479981647419359229227 := by
  unfold tailWord_2032170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18529832261950657962423491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49412886031868421233129309 18529832261950657962423491)
  ·
    refine ⟨27794748392925986943635237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18529832261950657962423491 27794748392925986943635237)
    ·
      refine ⟨5211515323673622551931607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27794748392925986943635237 5211515323673622551931607)
      ·
        refine ⟨7817272985510433827897411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211515323673622551931607 7817272985510433827897411)
        ·
          refine ⟨11725909478265650741846117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817272985510433827897411 11725909478265650741846117)
          ·
            refine ⟨2198608027174809514096147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11725909478265650741846117 2198608027174809514096147)
            ·
              refine ⟨3297912040762214271144221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198608027174809514096147 3297912040762214271144221)
              ·
                refine ⟨1236717015285830351679083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3297912040762214271144221 1236717015285830351679083)
                ·
                  refine ⟨1855075522928745527518625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236717015285830351679083 1855075522928745527518625)
                  ·
                    refine ⟨1391306642196559145638969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1855075522928745527518625 1391306642196559145638969)
                    ·
                      refine ⟨1043479981647419359229227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391306642196559145638969 1043479981647419359229227)
                      ·
                        rfl

theorem cell23_2032170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_2032170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032170 prefixEnd_2032170 := by exact prefixLift 2032170
  have htrace : WordTrace (prefixWord ++ tailWord_2032170) baseStart_2032170 baseEnd_2032170 := by
    simpa [prefixWord, tailWord_2032170, baseEnd_2032170] using wordTrace_append hprefix tailTrace_2032170
  have hstable : (prefixWord ++ tailWord_2032170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032170).length < 2 ^ (prefixWord ++ tailWord_2032170).sum := by decide
  have hdescent : baseEnd_2032170 < baseStart_2032170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032173 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2032173 : Nat := 118140960795 + 2032173 * 2 ^ 59
def prefixEnd_2032173 : Nat := 4983230072969 + 3 ^ 40 * 2032173 * 2
def baseEnd_2032173 : Nat := 1043481522089382847491713

theorem tailTrace_2032173 : CollatzResearch.WordTrace tailWord_2032173 prefixEnd_2032173 1043481522089382847491713 := by
  unfold tailWord_2032173
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119438466791763362053173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49412958977861175574702115 74119438466791763362053173)
  ·
    refine ⟨6948697356261727815192485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74119438466791763362053173 6948697356261727815192485)
    ·
      refine ⟨1302880754299073965348591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6948697356261727815192485 1302880754299073965348591)
      ·
        refine ⟨1954321131448610948022887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302880754299073965348591 1954321131448610948022887)
        ·
          refine ⟨2931481697172916422034331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954321131448610948022887 2931481697172916422034331)
          ·
            refine ⟨4397222545759374633051497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931481697172916422034331 4397222545759374633051497)
            ·
              refine ⟨3297916909319530974788623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397222545759374633051497 3297916909319530974788623)
              ·
                refine ⟨4946875363979296462182935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297916909319530974788623 4946875363979296462182935)
                ·
                  refine ⟨7420313045968944693274403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946875363979296462182935 7420313045968944693274403)
                  ·
                    refine ⟨11130469568953417039911605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420313045968944693274403 11130469568953417039911605)
                    ·
                      refine ⟨1043481522089382847491713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11130469568953417039911605 1043481522089382847491713)
                      ·
                        rfl

theorem cell23_2032173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2032173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032173 prefixEnd_2032173 := by exact prefixLift 2032173
  have htrace : WordTrace (prefixWord ++ tailWord_2032173) baseStart_2032173 baseEnd_2032173 := by
    simpa [prefixWord, tailWord_2032173, baseEnd_2032173] using wordTrace_append hprefix tailTrace_2032173
  have hstable : (prefixWord ++ tailWord_2032173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032173).length < 2 ^ (prefixWord ++ tailWord_2032173).sum := by decide
  have hdescent : baseEnd_2032173 < baseStart_2032173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032179 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 1, 3, 2]
def baseStart_2032179 : Nat := 118140960795 + 2032179 * 2 ^ 59
def prefixEnd_2032179 : Nat := 4983230072969 + 3 ^ 40 * 2032179 * 2
def baseEnd_2032179 : Nat := 1043484602973309824016685

theorem tailTrace_2032179 : CollatzResearch.WordTrace tailWord_2032179 prefixEnd_2032179 1043484602973309824016685 := by
  unfold tailWord_2032179
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119657304770026386771591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49413104869846684257847727 74119657304770026386771591)
  ·
    refine ⟨111179485957155039580157387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74119657304770026386771591 111179485957155039580157387)
    ·
      refine ⟨166769228935732559370236081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111179485957155039580157387 166769228935732559370236081)
      ·
        refine ⟨125076921701799419527677061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166769228935732559370236081 125076921701799419527677061)
        ·
          refine ⟨23451922819087391161439449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125076921701799419527677061 23451922819087391161439449)
          ·
            refine ⟨17588942114315543371079587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23451922819087391161439449 17588942114315543371079587)
            ·
              refine ⟨26383413171473315056619381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588942114315543371079587 26383413171473315056619381)
              ·
                refine ⟨2473444984825623286558067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26383413171473315056619381 2473444984825623286558067)
                ·
                  refine ⟨3710167477238434929837101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473444984825623286558067 3710167477238434929837101)
                  ·
                    refine ⟨1391312803964413098688913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710167477238434929837101 1391312803964413098688913)
                    ·
                      refine ⟨1043484602973309824016685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391312803964413098688913 1043484602973309824016685)
                      ·
                        rfl

theorem cell23_2032179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3, 2].length) (baseStart_2032179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032179 prefixEnd_2032179 := by exact prefixLift 2032179
  have htrace : WordTrace (prefixWord ++ tailWord_2032179) baseStart_2032179 baseEnd_2032179 := by
    simpa [prefixWord, tailWord_2032179, baseEnd_2032179] using wordTrace_append hprefix tailTrace_2032179
  have hstable : (prefixWord ++ tailWord_2032179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032179).length < 2 ^ (prefixWord ++ tailWord_2032179).sum := by decide
  have hdescent : baseEnd_2032179 < baseStart_2032179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032212 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2032212 : Nat := 118140960795 + 2032212 * 2 ^ 59
def prefixEnd_2032212 : Nat := 4983230072969 + 3 ^ 40 * 2032212 * 2
def baseEnd_2032212 : Nat := 1043501547834908194904033

theorem tailTrace_2032212 : CollatzResearch.WordTrace tailWord_2032212 prefixEnd_2032212 1043501547834908194904033 := by
  unfold tailWord_2032212
  simp only [CollatzResearch.WordTrace]
  refine ⟨37060430456825236511361445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49413907275766982015148593 37060430456825236511361445)
  ·
    refine ⟨6948830710654731845880271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37060430456825236511361445 6948830710654731845880271)
    ·
      refine ⟨10423246065982097768820407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6948830710654731845880271 10423246065982097768820407)
      ·
        refine ⟨15634869098973146653230611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10423246065982097768820407 15634869098973146653230611)
        ·
          refine ⟨23452303648459719979845917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15634869098973146653230611 23452303648459719979845917)
          ·
            refine ⟨8794613868172394992442219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23452303648459719979845917 8794613868172394992442219)
            ·
              refine ⟨13191920802258592488663329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794613868172394992442219 13191920802258592488663329)
              ·
                refine ⟨9893940601693944366497497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13191920802258592488663329 9893940601693944366497497)
                ·
                  refine ⟨7420455451270458274873123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893940601693944366497497 7420455451270458274873123)
                  ·
                    refine ⟨11130683176905687412309685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420455451270458274873123 11130683176905687412309685)
                    ·
                      refine ⟨1043501547834908194904033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11130683176905687412309685 1043501547834908194904033)
                      ·
                        rfl

theorem cell23_2032212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2032212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032212 prefixEnd_2032212 := by exact prefixLift 2032212
  have htrace : WordTrace (prefixWord ++ tailWord_2032212) baseStart_2032212 baseEnd_2032212 := by
    simpa [prefixWord, tailWord_2032212, baseEnd_2032212] using wordTrace_append hprefix tailTrace_2032212
  have hstable : (prefixWord ++ tailWord_2032212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032212).length < 2 ^ (prefixWord ++ tailWord_2032212).sum := by decide
  have hdescent : baseEnd_2032212 < baseStart_2032212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032215 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 9]
def baseStart_2032215 : Nat := 118140960795 + 2032215 * 2 ^ 59
def prefixEnd_2032215 : Nat := 4983230072969 + 3 ^ 40 * 2032215 * 2
def baseEnd_2032215 : Nat := 115944787586319075907391

theorem tailTrace_2032215 : CollatzResearch.WordTrace tailWord_2032215 prefixEnd_2032215 115944787586319075907391 := by
  unfold tailWord_2032215
  simp only [CollatzResearch.WordTrace]
  refine ⟨74120970332639604535082099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49413980221759736356721399 74120970332639604535082099)
  ·
    refine ⟨111181455498959406802623149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74120970332639604535082099 111181455498959406802623149)
    ·
      refine ⟨41693045812109777550983681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111181455498959406802623149 41693045812109777550983681)
      ·
        refine ⟨31269784359082333163237761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41693045812109777550983681 31269784359082333163237761)
        ·
          refine ⟨23452338269311749872428321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31269784359082333163237761 23452338269311749872428321)
          ·
            refine ⟨17589253701983812404321241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23452338269311749872428321 17589253701983812404321241)
            ·
              refine ⟨13191940276487859303240931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17589253701983812404321241 13191940276487859303240931)
              ·
                refine ⟨19787910414731788954861397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191940276487859303240931 19787910414731788954861397)
                ·
                  refine ⟨115944787586319075907391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19787910414731788954861397 115944787586319075907391)
                  ·
                    rfl

theorem cell23_2032215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 9].length) (baseStart_2032215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032215 prefixEnd_2032215 := by exact prefixLift 2032215
  have htrace : WordTrace (prefixWord ++ tailWord_2032215) baseStart_2032215 baseEnd_2032215 := by
    simpa [prefixWord, tailWord_2032215, baseEnd_2032215] using wordTrace_append hprefix tailTrace_2032215
  have hstable : (prefixWord ++ tailWord_2032215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032215).length < 2 ^ (prefixWord ++ tailWord_2032215).sum := by decide
  have hdescent : baseEnd_2032215 < baseStart_2032215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032249 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 5]
def baseStart_2032249 : Nat := 118140960795 + 2032249 * 2 ^ 59
def prefixEnd_2032249 : Nat := 4983230072969 + 3 ^ 40 * 2032249 * 2
def baseEnd_2032249 : Nat := 115946727402124950015707

theorem tailTrace_2032249 : CollatzResearch.WordTrace tailWord_2032249 prefixEnd_2032249 115946727402124950015707 := by
  unfold tailWord_2032249
  simp only [CollatzResearch.WordTrace]
  refine ⟨74122210414516428341819801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49414806943010952227879867 74122210414516428341819801)
  ·
    refine ⟨55591657810887321256364851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74122210414516428341819801 55591657810887321256364851)
    ·
      refine ⟨83387486716330981884547277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55591657810887321256364851 83387486716330981884547277)
      ·
        refine ⟨31270307518624118206705229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83387486716330981884547277 31270307518624118206705229)
        ·
          refine ⟨11726365319484044327514461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31270307518624118206705229 11726365319484044327514461)
          ·
            refine ⟨4397386994806516622817923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11726365319484044327514461 4397386994806516622817923)
            ·
              refine ⟨6596080492209774934226885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397386994806516622817923 6596080492209774934226885)
              ·
                refine ⟨1236765092289332800167541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6596080492209774934226885 1236765092289332800167541)
                ·
                  refine ⟨115946727402124950015707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1236765092289332800167541 115946727402124950015707)
                  ·
                    rfl

theorem cell23_2032249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 5].length) (baseStart_2032249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032249 prefixEnd_2032249 := by exact prefixLift 2032249
  have htrace : WordTrace (prefixWord ++ tailWord_2032249) baseStart_2032249 baseEnd_2032249 := by
    simpa [prefixWord, tailWord_2032249, baseEnd_2032249] using wordTrace_append hprefix tailTrace_2032249
  have hstable : (prefixWord ++ tailWord_2032249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032249).length < 2 ^ (prefixWord ++ tailWord_2032249).sum := by decide
  have hdescent : baseEnd_2032249 < baseStart_2032249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032255 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_2032255 : Nat := 118140960795 + 2032255 * 2 ^ 59
def prefixEnd_2032255 : Nat := 4983230072969 + 3 ^ 40 * 2032255 * 2
def baseEnd_2032255 : Nat := 1043523627503051526666335

theorem tailTrace_2032255 : CollatzResearch.WordTrace tailWord_2032255 prefixEnd_2032255 1043523627503051526666335 := by
  unfold tailWord_2032255
  simp only [CollatzResearch.WordTrace]
  refine ⟨74122429252494691366538219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49414952834996460911025479 74122429252494691366538219)
  ·
    refine ⟨111183643878742037049807329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74122429252494691366538219 111183643878742037049807329)
    ·
      refine ⟨83387732909056527787355497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111183643878742037049807329 83387732909056527787355497)
      ·
        refine ⟨62540799681792395840516623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83387732909056527787355497 62540799681792395840516623)
        ·
          refine ⟨93811199522688593760774935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62540799681792395840516623 93811199522688593760774935)
          ·
            refine ⟨140716799284032890641162403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93811199522688593760774935 140716799284032890641162403)
            ·
              refine ⟨211075198926049335961743605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140716799284032890641162403 211075198926049335961743605)
              ·
                refine ⟨19788299899317125246413463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211075198926049335961743605 19788299899317125246413463)
                ·
                  refine ⟨29682449848975687869620195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19788299899317125246413463 29682449848975687869620195)
                  ·
                    refine ⟨44523674773463531804430293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29682449848975687869620195 44523674773463531804430293)
                    ·
                      refine ⟨1043523627503051526666335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44523674773463531804430293 1043523627503051526666335)
                      ·
                        rfl

theorem cell23_2032255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_2032255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032255 prefixEnd_2032255 := by exact prefixLift 2032255
  have htrace : WordTrace (prefixWord ++ tailWord_2032255) baseStart_2032255 baseEnd_2032255 := by
    simpa [prefixWord, tailWord_2032255, baseEnd_2032255] using wordTrace_append hprefix tailTrace_2032255
  have hstable : (prefixWord ++ tailWord_2032255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032255).length < 2 ^ (prefixWord ++ tailWord_2032255).sum := by decide
  have hdescent : baseEnd_2032255 < baseStart_2032255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032275 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 8]
def baseStart_2032275 : Nat := 118140960795 + 2032275 * 2 ^ 59
def prefixEnd_2032275 : Nat := 4983230072969 + 3 ^ 40 * 2032275 * 2
def baseEnd_2032275 : Nat := 347844632372047149472081

theorem tailTrace_2032275 : CollatzResearch.WordTrace tailWord_2032275 prefixEnd_2032275 347844632372047149472081 := by
  unfold tailWord_2032275
  simp only [CollatzResearch.WordTrace]
  refine ⟨74123158712422234782266279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49415439141614823188177519 74123158712422234782266279)
  ·
    refine ⟨111184738068633352173399419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74123158712422234782266279 111184738068633352173399419)
    ·
      refine ⟨166777107102950028260099129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111184738068633352173399419 166777107102950028260099129)
      ·
        refine ⟨125082830327212521195074347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166777107102950028260099129 125082830327212521195074347)
        ·
          refine ⟨187624245490818781792611521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125082830327212521195074347 187624245490818781792611521)
          ·
            refine ⟨140718184118114086344458641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187624245490818781792611521 140718184118114086344458641)
            ·
              refine ⟨105538638088585564758343981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140718184118114086344458641 105538638088585564758343981)
              ·
                refine ⟨39576989283219586784378993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105538638088585564758343981 39576989283219586784378993)
                ·
                  refine ⟨29682741962414690088284245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39576989283219586784378993 29682741962414690088284245)
                  ·
                    refine ⟨347844632372047149472081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29682741962414690088284245 347844632372047149472081)
                    ·
                      rfl

theorem cell23_2032275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_2032275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032275 prefixEnd_2032275 := by exact prefixLift 2032275
  have htrace : WordTrace (prefixWord ++ tailWord_2032275) baseStart_2032275 baseEnd_2032275 := by
    simpa [prefixWord, tailWord_2032275, baseEnd_2032275] using wordTrace_append hprefix tailTrace_2032275
  have hstable : (prefixWord ++ tailWord_2032275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032275).length < 2 ^ (prefixWord ++ tailWord_2032275).sum := by decide
  have hdescent : baseEnd_2032275 < baseStart_2032275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032343 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 1, 4]
def baseStart_2032343 : Nat := 118140960795 + 2032343 * 2 ^ 59
def prefixEnd_2032343 : Nat := 4983230072969 + 3 ^ 40 * 2032343 * 2
def baseEnd_2032343 : Nat := 347856271266882394121977

theorem tailTrace_2032343 : CollatzResearch.WordTrace tailWord_2032343 prefixEnd_2032343 347856271266882394121977 := by
  unfold tailWord_2032343
  simp only [CollatzResearch.WordTrace]
  refine ⟨74125638876175882395741683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49417092584117254930494455 74125638876175882395741683)
  ·
    refine ⟨111188458314263823593612525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74125638876175882395741683 111188458314263823593612525)
    ·
      refine ⟨41695671867848933847604697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111188458314263823593612525 41695671867848933847604697)
      ·
        refine ⟨31271753900886700385703523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41695671867848933847604697 31271753900886700385703523)
        ·
          refine ⟨46907630851330050578555285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31271753900886700385703523 46907630851330050578555285)
          ·
            refine ⟨2198795196156096120869779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46907630851330050578555285 2198795196156096120869779)
            ·
              refine ⟨3298192794234144181304669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198795196156096120869779 3298192794234144181304669)
              ·
                refine ⟨1236822297837804067989251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298192794234144181304669 1236822297837804067989251)
                ·
                  refine ⟨1855233446756706101983877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236822297837804067989251 1855233446756706101983877)
                  ·
                    refine ⟨347856271266882394121977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855233446756706101983877 347856271266882394121977)
                    ·
                      rfl

theorem cell23_2032343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_2032343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032343 prefixEnd_2032343 := by exact prefixLift 2032343
  have htrace : WordTrace (prefixWord ++ tailWord_2032343) baseStart_2032343 baseEnd_2032343 := by
    simpa [prefixWord, tailWord_2032343, baseEnd_2032343] using wordTrace_append hprefix tailTrace_2032343
  have hstable : (prefixWord ++ tailWord_2032343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032343).length < 2 ^ (prefixWord ++ tailWord_2032343).sum := by decide
  have hdescent : baseEnd_2032343 < baseStart_2032343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032352 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_2032352 : Nat := 118140960795 + 2032352 * 2 ^ 59
def prefixEnd_2032352 : Nat := 4983230072969 + 3 ^ 40 * 2032352 * 2
def baseEnd_2032352 : Nat := 347857811708845882384463

theorem tailTrace_2032352 : CollatzResearch.WordTrace tailWord_2032352 prefixEnd_2032352 347857811708845882384463 := by
  unfold tailWord_2032352
  simp only [CollatzResearch.WordTrace]
  refine ⟨37062983566571638466409655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49417311422095517955212873 37062983566571638466409655)
  ·
    refine ⟨55594475349857457699614483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37062983566571638466409655 55594475349857457699614483)
    ·
      refine ⟨83391713024786186549421725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55594475349857457699614483 83391713024786186549421725)
      ·
        refine ⟨31271892384294819956033147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83391713024786186549421725 31271892384294819956033147)
        ·
          refine ⟨46907838576442229934049721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31271892384294819956033147 46907838576442229934049721)
          ·
            refine ⟨35180878932331672450537291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46907838576442229934049721 35180878932331672450537291)
            ·
              refine ⟨52771318398497508675805937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35180878932331672450537291 52771318398497508675805937)
              ·
                refine ⟨39578488798873131506854453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52771318398497508675805937 39578488798873131506854453)
                ·
                  refine ⟨3710483324894356078767605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39578488798873131506854453 3710483324894356078767605)
                  ·
                    refine ⟨347857811708845882384463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3710483324894356078767605 347857811708845882384463)
                    ·
                      rfl

theorem cell23_2032352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_2032352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032352 prefixEnd_2032352 := by exact prefixLift 2032352
  have htrace : WordTrace (prefixWord ++ tailWord_2032352) baseStart_2032352 baseEnd_2032352 := by
    simpa [prefixWord, tailWord_2032352, baseEnd_2032352] using wordTrace_append hprefix tailTrace_2032352
  have hstable : (prefixWord ++ tailWord_2032352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032352).length < 2 ^ (prefixWord ++ tailWord_2032352).sum := by decide
  have hdescent : baseEnd_2032352 < baseStart_2032352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032360 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 1, 4]
def baseStart_2032360 : Nat := 118140960795 + 2032360 * 2 ^ 59
def prefixEnd_2032360 : Nat := 4983230072969 + 3 ^ 40 * 2032360 * 2
def baseEnd_2032360 : Nat := 347859180990591205284451

theorem tailTrace_2032360 : CollatzResearch.WordTrace tailWord_2032360 prefixEnd_2032360 347859180990591205284451 := by
  unfold tailWord_2032360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37063129458557147149555267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49417505944742862866073689 37063129458557147149555267)
  ·
    refine ⟨55594694187835720724332901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37063129458557147149555267 55594694187835720724332901)
    ·
      refine ⟨10424005160219197635812419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55594694187835720724332901 10424005160219197635812419)
      ·
        refine ⟨15636007740328796453718629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424005160219197635812419 15636007740328796453718629)
        ·
          refine ⟨2931751451311649335072243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15636007740328796453718629 2931751451311649335072243)
          ·
            refine ⟨4397627176967474002608365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931751451311649335072243 4397627176967474002608365)
            ·
              refine ⟨1649110191362802750978137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4397627176967474002608365 1649110191362802750978137)
              ·
                refine ⟨1236832643522102063233603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649110191362802750978137 1236832643522102063233603)
                ·
                  refine ⟨1855248965283153094850405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236832643522102063233603 1855248965283153094850405)
                  ·
                    refine ⟨347859180990591205284451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855248965283153094850405 347859180990591205284451)
                    ·
                      rfl

theorem cell23_2032360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_2032360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032360 prefixEnd_2032360 := by exact prefixLift 2032360
  have htrace : WordTrace (prefixWord ++ tailWord_2032360) baseStart_2032360 baseEnd_2032360 := by
    simpa [prefixWord, tailWord_2032360, baseEnd_2032360] using wordTrace_append hprefix tailTrace_2032360
  have hstable : (prefixWord ++ tailWord_2032360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032360).length < 2 ^ (prefixWord ++ tailWord_2032360).sum := by decide
  have hdescent : baseEnd_2032360 < baseStart_2032360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032362 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2032362 : Nat := 118140960795 + 2032362 * 2 ^ 59
def prefixEnd_2032362 : Nat := 4983230072969 + 3 ^ 40 * 2032362 * 2
def baseEnd_2032362 : Nat := 1043578569933082608028343

theorem tailTrace_2032362 : CollatzResearch.WordTrace tailWord_2032362 prefixEnd_2032362 1043578569933082608028343 := by
  unfold tailWord_2032362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18531582965776762160170835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49417554575404699093788893 18531582965776762160170835)
  ·
    refine ⟨27797374448665143240256253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18531582965776762160170835 27797374448665143240256253)
    ·
      refine ⟨10424015418249428715096095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27797374448665143240256253 10424015418249428715096095)
      ·
        refine ⟨15636023127374143072644143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424015418249428715096095 15636023127374143072644143)
        ·
          refine ⟨23454034691061214608966215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15636023127374143072644143 23454034691061214608966215)
          ·
            refine ⟨35181052036591821913449323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23454034691061214608966215 35181052036591821913449323)
            ·
              refine ⟨52771578054887732870173985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35181052036591821913449323 52771578054887732870173985)
              ·
                refine ⟨39578683541165799652630489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52771578054887732870173985 39578683541165799652630489)
                ·
                  refine ⟨29684012655874349739472867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39578683541165799652630489 29684012655874349739472867)
                  ·
                    refine ⟨44526018983811524609209301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29684012655874349739472867 44526018983811524609209301)
                    ·
                      refine ⟨1043578569933082608028343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44526018983811524609209301 1043578569933082608028343)
                      ·
                        rfl

theorem cell23_2032362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2032362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032362 prefixEnd_2032362 := by exact prefixLift 2032362
  have htrace : WordTrace (prefixWord ++ tailWord_2032362) baseStart_2032362 baseEnd_2032362 := by
    simpa [prefixWord, tailWord_2032362, baseEnd_2032362] using wordTrace_append hprefix tailTrace_2032362
  have hstable : (prefixWord ++ tailWord_2032362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032362).length < 2 ^ (prefixWord ++ tailWord_2032362).sum := by decide
  have hdescent : baseEnd_2032362 < baseStart_2032362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032386 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2032386 : Nat := 118140960795 + 2032386 * 2 ^ 59
def prefixEnd_2032386 : Nat := 4983230072969 + 3 ^ 40 * 2032386 * 2
def baseEnd_2032386 : Nat := 347863631156263504709411

theorem tailTrace_2032386 : CollatzResearch.WordTrace tailWord_2032386 prefixEnd_2032386 347863631156263504709411 := by
  unfold tailWord_2032386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18531801803755025184889253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49418138143346733826371341 18531801803755025184889253)
  ·
    refine ⟨3474712838204067222166735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18531801803755025184889253 3474712838204067222166735)
    ·
      refine ⟨5212069257306100833250103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474712838204067222166735 5212069257306100833250103)
      ·
        refine ⟨7818103885959151249875155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212069257306100833250103 7818103885959151249875155)
        ·
          refine ⟨11727155828938726874812733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818103885959151249875155 11727155828938726874812733)
          ·
            refine ⟨4397683435852022578054775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11727155828938726874812733 4397683435852022578054775)
            ·
              refine ⟨6596525153778033867082163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397683435852022578054775 6596525153778033867082163)
              ·
                refine ⟨9894787730667050800623245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596525153778033867082163 9894787730667050800623245)
                ·
                  refine ⟨3710545399000144050233717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9894787730667050800623245 3710545399000144050233717)
                  ·
                    refine ⟨347863631156263504709411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3710545399000144050233717 347863631156263504709411)
                    ·
                      rfl

theorem cell23_2032386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2032386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032386 prefixEnd_2032386 := by exact prefixLift 2032386
  have htrace : WordTrace (prefixWord ++ tailWord_2032386) baseStart_2032386 baseEnd_2032386 := by
    simpa [prefixWord, tailWord_2032386, baseEnd_2032386] using wordTrace_append hprefix tailTrace_2032386
  have hstable : (prefixWord ++ tailWord_2032386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032386).length < 2 ^ (prefixWord ++ tailWord_2032386).sum := by decide
  have hdescent : baseEnd_2032386 < baseStart_2032386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032389 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_2032389 : Nat := 118140960795 + 2032389 * 2 ^ 59
def prefixEnd_2032389 : Nat := 4983230072969 + 3 ^ 40 * 2032389 * 2
def baseEnd_2032389 : Nat := 1043592433910754002390719

theorem tailTrace_2032389 : CollatzResearch.WordTrace tailWord_2032389 prefixEnd_2032389 1043592433910754002390719 := by
  unfold tailWord_2032389
  simp only [CollatzResearch.WordTrace]
  refine ⟨74127316634009232251916221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49418211089339488167944147 74127316634009232251916221)
  ·
    refine ⟨27797743737753462094468583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74127316634009232251916221 27797743737753462094468583)
    ·
      refine ⟨41696615606630193141702875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27797743737753462094468583 41696615606630193141702875)
      ·
        refine ⟨62544923409945289712554313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41696615606630193141702875 62544923409945289712554313)
        ·
          refine ⟨46908692557458967284415735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62544923409945289712554313 46908692557458967284415735)
          ·
            refine ⟨70363038836188450926623603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46908692557458967284415735 70363038836188450926623603)
            ·
              refine ⟨105544558254282676389935405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70363038836188450926623603 105544558254282676389935405)
              ·
                refine ⟨39579209345356003646225777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105544558254282676389935405 39579209345356003646225777)
                ·
                  refine ⟨29684407009017002734669333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39579209345356003646225777 29684407009017002734669333)
                  ·
                    refine ⟨1391456578547672003187625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29684407009017002734669333 1391456578547672003187625)
                    ·
                      refine ⟨1043592433910754002390719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391456578547672003187625 1043592433910754002390719)
                      ·
                        rfl

theorem cell23_2032389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_2032389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032389 prefixEnd_2032389 := by exact prefixLift 2032389
  have htrace : WordTrace (prefixWord ++ tailWord_2032389) baseStart_2032389 baseEnd_2032389 := by
    simpa [prefixWord, tailWord_2032389, baseEnd_2032389] using wordTrace_append hprefix tailTrace_2032389
  have hstable : (prefixWord ++ tailWord_2032389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032389).length < 2 ^ (prefixWord ++ tailWord_2032389).sum := by decide
  have hdescent : baseEnd_2032389 < baseStart_2032389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032412 : List Nat := [2, 2, 3, 1, 1, 14]
def baseStart_2032412 : Nat := 118140960795 + 2032412 * 2 ^ 59
def prefixEnd_2032412 : Nat := 4983230072969 + 3 ^ 40 * 2032412 * 2
def baseEnd_2032412 : Nat := 4294667670641182767091

theorem tailTrace_2032412 : CollatzResearch.WordTrace tailWord_2032412 prefixEnd_2032412 4294667670641182767091 := by
  unfold tailWord_2032412
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064077756462953590001745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49418770341950604786668993 37064077756462953590001745)
  ·
    refine ⟨27798058317347215192501309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37064077756462953590001745 27798058317347215192501309)
    ·
      refine ⟨10424271869005205697187991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27798058317347215192501309 10424271869005205697187991)
      ·
        refine ⟨15636407803507808545781987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424271869005205697187991 15636407803507808545781987)
        ·
          refine ⟨23454611705261712818672981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15636407803507808545781987 23454611705261712818672981)
          ·
            refine ⟨4294667670641182767091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 23454611705261712818672981 4294667670641182767091)
            ·
              rfl

theorem cell23_2032412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 14].length) (baseStart_2032412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032412 prefixEnd_2032412 := by exact prefixLift 2032412
  have htrace : WordTrace (prefixWord ++ tailWord_2032412) baseStart_2032412 baseEnd_2032412 := by
    simpa [prefixWord, tailWord_2032412, baseEnd_2032412] using wordTrace_append hprefix tailTrace_2032412
  have hstable : (prefixWord ++ tailWord_2032412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032412).length < 2 ^ (prefixWord ++ tailWord_2032412).sum := by decide
  have hdescent : baseEnd_2032412 < baseStart_2032412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032416 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_2032416 : Nat := 118140960795 + 2032416 * 2 ^ 59
def prefixEnd_2032416 : Nat := 4983230072969 + 3 ^ 40 * 2032416 * 2
def baseEnd_2032416 : Nat := 347868765962808465584365

theorem tailTrace_2032416 : CollatzResearch.WordTrace tailWord_2032416 prefixEnd_2032416 347868765962808465584365 := by
  unfold tailWord_2032416
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064150702455707931574551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49418867603274277242099401 37064150702455707931574551)
  ·
    refine ⟨55596226053683561897361827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37064150702455707931574551 55596226053683561897361827)
    ·
      refine ⟨83394339080525342846042741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55596226053683561897361827 83394339080525342846042741)
      ·
        refine ⟨7818219288799250891816507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83394339080525342846042741 7818219288799250891816507)
        ·
          refine ⟨11727328933198876337724761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818219288799250891816507 11727328933198876337724761)
          ·
            refine ⟨8795496699899157253293571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11727328933198876337724761 8795496699899157253293571)
            ·
              refine ⟨13193245049848735879940357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795496699899157253293571 13193245049848735879940357)
              ·
                refine ⟨2473733446846637977488817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13193245049848735879940357 2473733446846637977488817)
                ·
                  refine ⟨1855300085134978483116613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473733446846637977488817 1855300085134978483116613)
                  ·
                    refine ⟨347868765962808465584365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855300085134978483116613 347868765962808465584365)
                    ·
                      rfl

theorem cell23_2032416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_2032416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032416 prefixEnd_2032416 := by exact prefixLift 2032416
  have htrace : WordTrace (prefixWord ++ tailWord_2032416) baseStart_2032416 baseEnd_2032416 := by
    simpa [prefixWord, tailWord_2032416, baseEnd_2032416] using wordTrace_append hprefix tailTrace_2032416
  have hstable : (prefixWord ++ tailWord_2032416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032416).length < 2 ^ (prefixWord ++ tailWord_2032416).sum := by decide
  have hdescent : baseEnd_2032416 < baseStart_2032416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032432 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_2032432 : Nat := 118140960795 + 2032432 * 2 ^ 59
def prefixEnd_2032432 : Nat := 4983230072969 + 3 ^ 40 * 2032432 * 2
def baseEnd_2032432 : Nat := 1043614513578897334153021

theorem tailTrace_2032432 : CollatzResearch.WordTrace tailWord_2032432 prefixEnd_2032432 1043614513578897334153021 := by
  unfold tailWord_2032432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064442486426725297865775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49419256648568967063821033 37064442486426725297865775)
  ·
    refine ⟨55596663729640087946798663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37064442486426725297865775 55596663729640087946798663)
    ·
      refine ⟨83394995594460131920197995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55596663729640087946798663 83394995594460131920197995)
      ·
        refine ⟨125092493391690197880296993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83394995594460131920197995 125092493391690197880296993)
        ·
          refine ⟨93819370043767648410222745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125092493391690197880296993 93819370043767648410222745)
          ·
            refine ⟨70364527532825736307667059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93819370043767648410222745 70364527532825736307667059)
            ·
              refine ⟨105546791299238604461500589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70364527532825736307667059 105546791299238604461500589)
              ·
                refine ⟨39580046737214476673062721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105546791299238604461500589 39580046737214476673062721)
                ·
                  refine ⟨29685035052910857504797041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39580046737214476673062721 29685035052910857504797041)
                  ·
                    refine ⟨22263776289683143128597781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29685035052910857504797041 22263776289683143128597781)
                    ·
                      refine ⟨1043614513578897334153021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22263776289683143128597781 1043614513578897334153021)
                      ·
                        rfl

theorem cell23_2032432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_2032432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032432 prefixEnd_2032432 := by exact prefixLift 2032432
  have htrace : WordTrace (prefixWord ++ tailWord_2032432) baseStart_2032432 baseEnd_2032432 := by
    simpa [prefixWord, tailWord_2032432, baseEnd_2032432] using wordTrace_append hprefix tailTrace_2032432
  have hstable : (prefixWord ++ tailWord_2032432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032432).length < 2 ^ (prefixWord ++ tailWord_2032432).sum := by decide
  have hdescent : baseEnd_2032432 < baseStart_2032432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032454 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2032454 : Nat := 118140960795 + 2032454 * 2 ^ 59
def prefixEnd_2032454 : Nat := 4983230072969 + 3 ^ 40 * 2032454 * 2
def baseEnd_2032454 : Nat := 347875270051098749359307

theorem tailTrace_2032454 : CollatzResearch.WordTrace tailWord_2032454 prefixEnd_2032454 347875270051098749359307 := by
  unfold tailWord_2032454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316552730586679636032263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49419791585849165568688277 2316552730586679636032263)
  ·
    refine ⟨3474829095880019454048395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316552730586679636032263 3474829095880019454048395)
    ·
      refine ⟨5212243643820029181072593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474829095880019454048395 5212243643820029181072593)
      ·
        refine ⟨3909182732865021885804445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5212243643820029181072593 3909182732865021885804445)
        ·
          refine ⟨1465943524824383207176667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3909182732865021885804445 1465943524824383207176667)
          ·
            refine ⟨2198915287236574810765001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465943524824383207176667 2198915287236574810765001)
            ·
              refine ⟨1649186465427431108073751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198915287236574810765001 1649186465427431108073751)
              ·
                refine ⟨2473779698141146662110627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649186465427431108073751 2473779698141146662110627)
                ·
                  refine ⟨3710669547211719993165941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473779698141146662110627 3710669547211719993165941)
                  ·
                    refine ⟨347875270051098749359307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3710669547211719993165941 347875270051098749359307)
                    ·
                      rfl

theorem cell23_2032454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2032454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032454 prefixEnd_2032454 := by exact prefixLift 2032454
  have htrace : WordTrace (prefixWord ++ tailWord_2032454) baseStart_2032454 baseEnd_2032454 := by
    simpa [prefixWord, tailWord_2032454, baseEnd_2032454] using wordTrace_append hprefix tailTrace_2032454
  have hstable : (prefixWord ++ tailWord_2032454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032454).length < 2 ^ (prefixWord ++ tailWord_2032454).sum := by decide
  have hdescent : baseEnd_2032454 < baseStart_2032454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032456 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_2032456 : Nat := 118140960795 + 2032456 * 2 ^ 59
def prefixEnd_2032456 : Nat := 4983230072969 + 3 ^ 40 * 2032456 * 2
def baseEnd_2032456 : Nat := 1043626837114605240252911

theorem tailTrace_2032456 : CollatzResearch.WordTrace tailWord_2032456 prefixEnd_2032456 1043626837114605240252911 := by
  unfold tailWord_2032456
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064880162383251347302611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49419840216511001796403481 37064880162383251347302611)
  ·
    refine ⟨55597320243574877020953917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37064880162383251347302611 55597320243574877020953917)
    ·
      refine ⟨20848995091340578882857719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55597320243574877020953917 20848995091340578882857719)
      ·
        refine ⟨31273492637010868324286579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20848995091340578882857719 31273492637010868324286579)
        ·
          refine ⟨46910238955516302486429869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31273492637010868324286579 46910238955516302486429869)
          ·
            refine ⟨17591339608318613432411201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46910238955516302486429869 17591339608318613432411201)
            ·
              refine ⟨13193504706238960074308401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17591339608318613432411201 13193504706238960074308401)
              ·
                refine ⟨9895128529679220055731301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13193504706238960074308401 9895128529679220055731301)
                ·
                  refine ⟨1855336599314853760449619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9895128529679220055731301 1855336599314853760449619)
                  ·
                    refine ⟨2783004898972280640674429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855336599314853760449619 2783004898972280640674429)
                    ·
                      refine ⟨1043626837114605240252911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783004898972280640674429 1043626837114605240252911)
                      ·
                        rfl

theorem cell23_2032456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_2032456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032456 prefixEnd_2032456 := by exact prefixLift 2032456
  have htrace : WordTrace (prefixWord ++ tailWord_2032456) baseStart_2032456 baseEnd_2032456 := by
    simpa [prefixWord, tailWord_2032456, baseEnd_2032456] using wordTrace_append hprefix tailTrace_2032456
  have hstable : (prefixWord ++ tailWord_2032456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032456).length < 2 ^ (prefixWord ++ tailWord_2032456).sum := by decide
  have hdescent : baseEnd_2032456 < baseStart_2032456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032460 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2032460 : Nat := 118140960795 + 2032460 * 2 ^ 59
def prefixEnd_2032460 : Nat := 4983230072969 + 3 ^ 40 * 2032460 * 2
def baseEnd_2032460 : Nat := 1043628891037223224602893

theorem tailTrace_2032460 : CollatzResearch.WordTrace tailWord_2032460 prefixEnd_2032460 1043628891037223224602893 := by
  unfold tailWord_2032460
  simp only [CollatzResearch.WordTrace]
  refine ⟨37064953108376005688875417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49419937477834674251833889 37064953108376005688875417)
  ·
    refine ⟨27798714831282004266656563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37064953108376005688875417 27798714831282004266656563)
    ·
      refine ⟨41698072246923006399984845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27798714831282004266656563 41698072246923006399984845)
      ·
        refine ⟨15636777092596127399994317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41698072246923006399984845 15636777092596127399994317)
        ·
          refine ⟨5863791409723547774997869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15636777092596127399994317 5863791409723547774997869)
          ·
            refine ⟨2198921778646330415624201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5863791409723547774997869 2198921778646330415624201)
            ·
              refine ⟨1649191333984747811718151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198921778646330415624201 1649191333984747811718151)
              ·
                refine ⟨2473787000977121717577227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649191333984747811718151 2473787000977121717577227)
                ·
                  refine ⟨3710680501465682576365841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473787000977121717577227 3710680501465682576365841)
                  ·
                    refine ⟨2783010376099261932274381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710680501465682576365841 2783010376099261932274381)
                    ·
                      refine ⟨1043628891037223224602893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783010376099261932274381 1043628891037223224602893)
                      ·
                        rfl

theorem cell23_2032460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2032460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032460 prefixEnd_2032460 := by exact prefixLift 2032460
  have htrace : WordTrace (prefixWord ++ tailWord_2032460) baseStart_2032460 baseEnd_2032460 := by
    simpa [prefixWord, tailWord_2032460, baseEnd_2032460] using wordTrace_append hprefix tailTrace_2032460
  have hstable : (prefixWord ++ tailWord_2032460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032460).length < 2 ^ (prefixWord ++ tailWord_2032460).sum := by decide
  have hdescent : baseEnd_2032460 < baseStart_2032460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032473 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 3]
def baseStart_2032473 : Nat := 118140960795 + 2032473 * 2 ^ 59
def prefixEnd_2032473 : Nat := 4983230072969 + 3 ^ 40 * 2032473 * 2
def baseEnd_2032473 : Nat := 1043635566285731673740333

theorem tailTrace_2032473 : CollatzResearch.WordTrace tailWord_2032473 prefixEnd_2032473 1043635566285731673740333 := by
  unfold tailWord_2032473
  simp only [CollatzResearch.WordTrace]
  refine ⟨74130380365704914597974073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49420253577136609731982715 74130380365704914597974073)
  ·
    refine ⟨55597785274278685948480555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74130380365704914597974073 55597785274278685948480555)
    ·
      refine ⟨83396677911418028922720833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55597785274278685948480555 83396677911418028922720833)
      ·
        refine ⟨62547508433563521692040625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83396677911418028922720833 62547508433563521692040625)
        ·
          refine ⟨46910631325172641269030469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62547508433563521692040625 46910631325172641269030469)
          ·
            refine ⟨8795743373469870237943213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46910631325172641269030469 8795743373469870237943213)
            ·
              refine ⟨3298403765051201339228705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8795743373469870237943213 3298403765051201339228705)
              ·
                refine ⟨2473802823788401004421529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298403765051201339228705 2473802823788401004421529)
                ·
                  refine ⟨1855352117841300753316147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473802823788401004421529 1855352117841300753316147)
                  ·
                    refine ⟨2783028176761951129974221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855352117841300753316147 2783028176761951129974221)
                    ·
                      refine ⟨1043635566285731673740333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783028176761951129974221 1043635566285731673740333)
                      ·
                        rfl

theorem cell23_2032473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_2032473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032473 prefixEnd_2032473 := by exact prefixLift 2032473
  have htrace : WordTrace (prefixWord ++ tailWord_2032473) baseStart_2032473 baseEnd_2032473 := by
    simpa [prefixWord, tailWord_2032473, baseEnd_2032473] using wordTrace_append hprefix tailTrace_2032473
  have hstable : (prefixWord ++ tailWord_2032473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032473).length < 2 ^ (prefixWord ++ tailWord_2032473).sum := by decide
  have hdescent : baseEnd_2032473 < baseStart_2032473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032499 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3]
def baseStart_2032499 : Nat := 118140960795 + 2032499 * 2 ^ 59
def prefixEnd_2032499 : Nat := 4983230072969 + 3 ^ 40 * 2032499 * 2
def baseEnd_2032499 : Nat := 1043648916782748572015213

theorem tailTrace_2032499 : CollatzResearch.WordTrace tailWord_2032499 prefixEnd_2032499 1043648916782748572015213 := by
  unfold tailWord_2032499
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131328663610721038420551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49420885775740480692280367 74131328663610721038420551)
  ·
    refine ⟨111196992995416081557630827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74131328663610721038420551 111196992995416081557630827)
    ·
      refine ⟨166795489493124122336446241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111196992995416081557630827 166795489493124122336446241)
      ·
        refine ⟨125096617119843091752334681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166795489493124122336446241 125096617119843091752334681)
        ·
          refine ⟨93822462839882318814251011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125096617119843091752334681 93822462839882318814251011)
          ·
            refine ⟨140733694259823478221376517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93822462839882318814251011 140733694259823478221376517)
            ·
              refine ⟨26387567673716902166508097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140733694259823478221376517 26387567673716902166508097)
              ·
                refine ⟨19790675755287676624881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26387567673716902166508097 19790675755287676624881073)
                ·
                  refine ⟨14843006816465757468660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19790675755287676624881073 14843006816465757468660805)
                  ·
                    refine ⟨2783063778087329525373901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14843006816465757468660805 2783063778087329525373901)
                    ·
                      refine ⟨1043648916782748572015213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783063778087329525373901 1043648916782748572015213)
                      ·
                        rfl

theorem cell23_2032499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_2032499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032499 prefixEnd_2032499 := by exact prefixLift 2032499
  have htrace : WordTrace (prefixWord ++ tailWord_2032499) baseStart_2032499 baseEnd_2032499 := by
    simpa [prefixWord, tailWord_2032499, baseEnd_2032499] using wordTrace_append hprefix tailTrace_2032499
  have hstable : (prefixWord ++ tailWord_2032499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032499).length < 2 ^ (prefixWord ++ tailWord_2032499).sum := by decide
  have hdescent : baseEnd_2032499 < baseStart_2032499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032509 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2032509 : Nat := 118140960795 + 2032509 * 2 ^ 59
def prefixEnd_2032509 : Nat := 4983230072969 + 3 ^ 40 * 2032509 * 2
def baseEnd_2032509 : Nat := 1043654051589293532890167

theorem tailTrace_2032509 : CollatzResearch.WordTrace tailWord_2032509 prefixEnd_2032509 1043654051589293532890167 := by
  unfold tailWord_2032509
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131693393574492746284581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49421128929049661830856387 74131693393574492746284581)
  ·
    refine ⟨13899692511295217389928359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74131693393574492746284581 13899692511295217389928359)
    ·
      refine ⟨20849538766942826084892539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13899692511295217389928359 20849538766942826084892539)
      ·
        refine ⟨31274308150414239127338809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20849538766942826084892539 31274308150414239127338809)
        ·
          refine ⟨23455731112810679345504107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31274308150414239127338809 23455731112810679345504107)
          ·
            refine ⟨35183596669216019018256161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23455731112810679345504107 35183596669216019018256161)
            ·
              refine ⟨26387697501912014263692121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35183596669216019018256161 26387697501912014263692121)
              ·
                refine ⟨19790773126434010697769091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26387697501912014263692121 19790773126434010697769091)
                ·
                  refine ⟨29686159689651016046653637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19790773126434010697769091 29686159689651016046653637)
                  ·
                    refine ⟨5566154941809565508747557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29686159689651016046653637 5566154941809565508747557)
                    ·
                      refine ⟨1043654051589293532890167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5566154941809565508747557 1043654051589293532890167)
                      ·
                        rfl

theorem cell23_2032509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2032509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032509 prefixEnd_2032509 := by exact prefixLift 2032509
  have htrace : WordTrace (prefixWord ++ tailWord_2032509) baseStart_2032509 baseEnd_2032509 := by
    simpa [prefixWord, tailWord_2032509, baseEnd_2032509] using wordTrace_append hprefix tailTrace_2032509
  have hstable : (prefixWord ++ tailWord_2032509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032509).length < 2 ^ (prefixWord ++ tailWord_2032509).sum := by decide
  have hdescent : baseEnd_2032509 < baseStart_2032509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032556 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_2032556 : Nat := 118140960795 + 2032556 * 2 ^ 59
def prefixEnd_2032556 : Nat := 4983230072969 + 3 ^ 40 * 2032556 * 2
def baseEnd_2032556 : Nat := 1043678185180054849002451

theorem tailTrace_2032556 : CollatzResearch.WordTrace tailWord_2032556 prefixEnd_2032556 1043678185180054849002451 := by
  unfold tailWord_2032556
  simp only [CollatzResearch.WordTrace]
  refine ⟨37066703812202109886622761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49422271749602813182163681 37066703812202109886622761)
  ·
    refine ⟨27800027859151582414967071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37066703812202109886622761 27800027859151582414967071)
    ·
      refine ⟨41700041788727373622450607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27800027859151582414967071 41700041788727373622450607)
      ·
        refine ⟨62550062683091060433675911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41700041788727373622450607 62550062683091060433675911)
        ·
          refine ⟨93825094024636590650513867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62550062683091060433675911 93825094024636590650513867)
          ·
            refine ⟨140737641036954885975770801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93825094024636590650513867 140737641036954885975770801)
            ·
              refine ⟨105553230777716164481828101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140737641036954885975770801 105553230777716164481828101)
              ·
                refine ⟨19791230770821780840342769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105553230777716164481828101 19791230770821780840342769)
                ·
                  refine ⟨14843423078116335630257077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19791230770821780840342769 14843423078116335630257077)
                  ·
                    refine ⟨1391570913573406465336601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14843423078116335630257077 1391570913573406465336601)
                    ·
                      refine ⟨1043678185180054849002451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391570913573406465336601 1043678185180054849002451)
                      ·
                        rfl

theorem cell23_2032556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_2032556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032556 prefixEnd_2032556 := by exact prefixLift 2032556
  have htrace : WordTrace (prefixWord ++ tailWord_2032556) baseStart_2032556 baseEnd_2032556 := by
    simpa [prefixWord, tailWord_2032556, baseEnd_2032556] using wordTrace_append hprefix tailTrace_2032556
  have hstable : (prefixWord ++ tailWord_2032556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032556).length < 2 ^ (prefixWord ++ tailWord_2032556).sum := by decide
  have hdescent : baseEnd_2032556 < baseStart_2032556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032599 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2032599 : Nat := 118140960795 + 2032599 * 2 ^ 59
def prefixEnd_2032599 : Nat := 4983230072969 + 3 ^ 40 * 2032599 * 2
def baseEnd_2032599 : Nat := 1043700264848198180764753

theorem tailTrace_2032599 : CollatzResearch.WordTrace tailWord_2032599 prefixEnd_2032599 1043700264848198180764753 := by
  unfold tailWord_2032599
  simp only [CollatzResearch.WordTrace]
  refine ⟨74134975963248438117060851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49423317308832292078040567 74134975963248438117060851)
  ·
    refine ⟨111202463944872657175591277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74134975963248438117060851 111202463944872657175591277)
    ·
      refine ⟨41700923979327246440846729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111202463944872657175591277 41700923979327246440846729)
      ·
        refine ⟨31275692984495434830635047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41700923979327246440846729 31275692984495434830635047)
        ·
          refine ⟨46913539476743152245952571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31275692984495434830635047 46913539476743152245952571)
          ·
            refine ⟨70370309215114728368928857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46913539476743152245952571 70370309215114728368928857)
            ·
              refine ⟨52777731911336046276696643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70370309215114728368928857 52777731911336046276696643)
              ·
                refine ⟨79166597867004069415044965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52777731911336046276696643 79166597867004069415044965)
                ·
                  refine ⟨14843737100063263015320931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79166597867004069415044965 14843737100063263015320931)
                  ·
                    refine ⟨22265605650094894522981397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14843737100063263015320931 22265605650094894522981397)
                    ·
                      refine ⟨1043700264848198180764753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22265605650094894522981397 1043700264848198180764753)
                      ·
                        rfl

theorem cell23_2032599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2032599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032599 prefixEnd_2032599 := by exact prefixLift 2032599
  have htrace : WordTrace (prefixWord ++ tailWord_2032599) baseStart_2032599 baseEnd_2032599 := by
    simpa [prefixWord, tailWord_2032599, baseEnd_2032599] using wordTrace_append hprefix tailTrace_2032599
  have hstable : (prefixWord ++ tailWord_2032599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032599).length < 2 ^ (prefixWord ++ tailWord_2032599).sum := by decide
  have hdescent : baseEnd_2032599 < baseStart_2032599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032609 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 10]
def baseStart_2032609 : Nat := 118140960795 + 2032609 * 2 ^ 59
def prefixEnd_2032609 : Nat := 4983230072969 + 3 ^ 40 * 2032609 * 2
def baseEnd_2032609 : Nat := 115967266628304793515523

theorem tailTrace_2032609 : CollatzResearch.WordTrace tailWord_2032609 prefixEnd_2032609 115967266628304793515523 := by
  unfold tailWord_2032609
  simp only [CollatzResearch.WordTrace]
  refine ⟨74135340693212209824924881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49423560462141473216616587 74135340693212209824924881)
  ·
    refine ⟨55601505519909157368693661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74135340693212209824924881 55601505519909157368693661)
    ·
      refine ⟨20850564569965934013260123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55601505519909157368693661 20850564569965934013260123)
      ·
        refine ⟨31275846854948901019890185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20850564569965934013260123 31275846854948901019890185)
        ·
          refine ⟨23456885141211675764917639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31275846854948901019890185 23456885141211675764917639)
          ·
            refine ⟨35185327711817513647376459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23456885141211675764917639 35185327711817513647376459)
            ·
              refine ⟨52777991567726270471064689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35185327711817513647376459 52777991567726270471064689)
              ·
                refine ⟨39583493675794702853298517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52777991567726270471064689 39583493675794702853298517)
                ·
                  refine ⟨115967266628304793515523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 39583493675794702853298517 115967266628304793515523)
                  ·
                    rfl

theorem cell23_2032609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_2032609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032609 prefixEnd_2032609 := by exact prefixLift 2032609
  have htrace : WordTrace (prefixWord ++ tailWord_2032609) baseStart_2032609 baseEnd_2032609 := by
    simpa [prefixWord, tailWord_2032609, baseEnd_2032609] using wordTrace_append hprefix tailTrace_2032609
  have hstable : (prefixWord ++ tailWord_2032609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032609).length < 2 ^ (prefixWord ++ tailWord_2032609).sum := by decide
  have hdescent : baseEnd_2032609 < baseStart_2032609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032623 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_2032623 : Nat := 118140960795 + 2032623 * 2 ^ 59
def prefixEnd_2032623 : Nat := 4983230072969 + 3 ^ 40 * 2032623 * 2
def baseEnd_2032623 : Nat := 1043712588383906086864643

theorem tailTrace_2032623 : CollatzResearch.WordTrace tailWord_2032623 prefixEnd_2032623 1043712588383906086864643 := by
  unfold tailWord_2032623
  simp only [CollatzResearch.WordTrace]
  refine ⟨74135851315161490215934523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49423900876774326810623015 74135851315161490215934523)
  ·
    refine ⟨111203776972742235323901785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74135851315161490215934523 111203776972742235323901785)
    ·
      refine ⟨83402832729556676492926339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111203776972742235323901785 83402832729556676492926339)
      ·
        refine ⟨125104249094335014739389509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83402832729556676492926339 125104249094335014739389509)
        ·
          refine ⟨23457046705187815263635533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125104249094335014739389509 23457046705187815263635533)
          ·
            refine ⟨8796392514445430723863325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23457046705187815263635533 8796392514445430723863325)
            ·
              refine ⟨3298647192917036521448747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8796392514445430723863325 3298647192917036521448747)
              ·
                refine ⟨4947970789375554782173121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298647192917036521448747 4947970789375554782173121)
                ·
                  refine ⟨3710978092031666086629841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947970789375554782173121 3710978092031666086629841)
                  ·
                    refine ⟨2783233569023749564972381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710978092031666086629841 2783233569023749564972381)
                    ·
                      refine ⟨1043712588383906086864643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783233569023749564972381 1043712588383906086864643)
                      ·
                        rfl

theorem cell23_2032623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_2032623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032623 prefixEnd_2032623 := by exact prefixLift 2032623
  have htrace : WordTrace (prefixWord ++ tailWord_2032623) baseStart_2032623 baseEnd_2032623 := by
    simpa [prefixWord, tailWord_2032623, baseEnd_2032623] using wordTrace_append hprefix tailTrace_2032623
  have hstable : (prefixWord ++ tailWord_2032623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032623).length < 2 ^ (prefixWord ++ tailWord_2032623).sum := by decide
  have hdescent : baseEnd_2032623 < baseStart_2032623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032673 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2032673 : Nat := 118140960795 + 2032673 * 2 ^ 59
def prefixEnd_2032673 : Nat := 4983230072969 + 3 ^ 40 * 2032673 * 2
def baseEnd_2032673 : Nat := 347912754138876963746471

theorem tailTrace_2032673 : CollatzResearch.WordTrace tailWord_2032673 prefixEnd_2032673 347912754138876963746471 := by
  unfold tailWord_2032673
  simp only [CollatzResearch.WordTrace]
  refine ⟨74137674964980348755254673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49425116643320232503503115 74137674964980348755254673)
  ·
    refine ⟨55603256223735261566441005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74137674964980348755254673 55603256223735261566441005)
    ·
      refine ⟨20851221083900723087415377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55603256223735261566441005 20851221083900723087415377)
      ·
        refine ⟨15638415812925542315561533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20851221083900723087415377 15638415812925542315561533)
        ·
          refine ⟨5864405929847078368335575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15638415812925542315561533 5864405929847078368335575)
          ·
            refine ⟨8796608894770617552503363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864405929847078368335575 8796608894770617552503363)
            ·
              refine ⟨13194913342155926328755045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796608894770617552503363 13194913342155926328755045)
              ·
                refine ⟨2474046251654236186641571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13194913342155926328755045 2474046251654236186641571)
                ·
                  refine ⟨3711069377481354279962357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474046251654236186641571 3711069377481354279962357)
                  ·
                    refine ⟨347912754138876963746471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3711069377481354279962357 347912754138876963746471)
                    ·
                      rfl

theorem cell23_2032673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2032673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032673 prefixEnd_2032673 := by exact prefixLift 2032673
  have htrace : WordTrace (prefixWord ++ tailWord_2032673) baseStart_2032673 baseEnd_2032673 := by
    simpa [prefixWord, tailWord_2032673, baseEnd_2032673] using wordTrace_append hprefix tailTrace_2032673
  have hstable : (prefixWord ++ tailWord_2032673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032673).length < 2 ^ (prefixWord ++ tailWord_2032673).sum := by decide
  have hdescent : baseEnd_2032673 < baseStart_2032673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032703 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 2, 4]
def baseStart_2032703 : Nat := 118140960795 + 2032703 * 2 ^ 59
def prefixEnd_2032703 : Nat := 4983230072969 + 3 ^ 40 * 2032703 * 2
def baseEnd_2032703 : Nat := 347917888945421924621425

theorem tailTrace_2032703 : CollatzResearch.WordTrace tailWord_2032703 prefixEnd_2032703 347917888945421924621425 := by
  unfold tailWord_2032703
  simp only [CollatzResearch.WordTrace]
  refine ⟨74138769154871663878846763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49425846103247775919231175 74138769154871663878846763)
  ·
    refine ⟨111208153732307495818270145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74138769154871663878846763 111208153732307495818270145)
    ·
      refine ⟨83406115299230621863702609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111208153732307495818270145 83406115299230621863702609)
      ·
        refine ⟨62554586474422966397776957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83406115299230621863702609 62554586474422966397776957)
        ·
          refine ⟨23457969927908612399166359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62554586474422966397776957 23457969927908612399166359)
          ·
            refine ⟨35186954891862918598749539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457969927908612399166359 35186954891862918598749539)
            ·
              refine ⟨52780432337794377898124309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35186954891862918598749539 52780432337794377898124309)
              ·
                refine ⟨2474082765834111463974577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52780432337794377898124309 2474082765834111463974577)
                ·
                  refine ⟨1855562074375583597980933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474082765834111463974577 1855562074375583597980933)
                  ·
                    refine ⟨347917888945421924621425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855562074375583597980933 347917888945421924621425)
                    ·
                      rfl

theorem cell23_2032703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_2032703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032703 prefixEnd_2032703 := by exact prefixLift 2032703
  have htrace : WordTrace (prefixWord ++ tailWord_2032703) baseStart_2032703 baseEnd_2032703 := by
    simpa [prefixWord, tailWord_2032703, baseEnd_2032703] using wordTrace_append hprefix tailTrace_2032703
  have hstable : (prefixWord ++ tailWord_2032703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032703).length < 2 ^ (prefixWord ++ tailWord_2032703).sum := by decide
  have hdescent : baseEnd_2032703 < baseStart_2032703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032743 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2032743 : Nat := 118140960795 + 2032743 * 2 ^ 59
def prefixEnd_2032743 : Nat := 4983230072969 + 3 ^ 40 * 2032743 * 2
def baseEnd_2032743 : Nat := 1043774206062445617364091

theorem tailTrace_2032743 : CollatzResearch.WordTrace tailWord_2032743 prefixEnd_2032743 1043774206062445617364091 := by
  unfold tailWord_2032743
  simp only [CollatzResearch.WordTrace]
  refine ⟨74140228074726750710302883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49426818716484500473535255 74140228074726750710302883)
  ·
    refine ⟨111210342112090126065454325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74140228074726750710302883 111210342112090126065454325)
    ·
      refine ⟨10425969573008449318636343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111210342112090126065454325 10425969573008449318636343)
      ·
        refine ⟨15638954359512673977954515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10425969573008449318636343 15638954359512673977954515)
        ·
          refine ⟨23458431539269010966931773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638954359512673977954515 23458431539269010966931773)
          ·
            refine ⟨8796911827225879112599415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23458431539269010966931773 8796911827225879112599415)
            ·
              refine ⟨13195367740838818668899123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796911827225879112599415 13195367740838818668899123)
              ·
                refine ⟨19793051611258228003348685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195367740838818668899123 19793051611258228003348685)
                ·
                  refine ⟨7422394354221835501255757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19793051611258228003348685 7422394354221835501255757)
                  ·
                    refine ⟨2783397882833188312970909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7422394354221835501255757 2783397882833188312970909)
                    ·
                      refine ⟨1043774206062445617364091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783397882833188312970909 1043774206062445617364091)
                      ·
                        rfl

theorem cell23_2032743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2032743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032743 prefixEnd_2032743 := by exact prefixLift 2032743
  have htrace : WordTrace (prefixWord ++ tailWord_2032743) baseStart_2032743 baseEnd_2032743 := by
    simpa [prefixWord, tailWord_2032743, baseEnd_2032743] using wordTrace_append hprefix tailTrace_2032743
  have hstable : (prefixWord ++ tailWord_2032743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032743).length < 2 ^ (prefixWord ++ tailWord_2032743).sum := by decide
  have hdescent : baseEnd_2032743 < baseStart_2032743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032744 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2032744 : Nat := 118140960795 + 2032744 * 2 ^ 59
def prefixEnd_2032744 : Nat := 4983230072969 + 3 ^ 40 * 2032744 * 2
def baseEnd_2032744 : Nat := 1043774719543100113451587

theorem tailTrace_2032744 : CollatzResearch.WordTrace tailWord_2032744 prefixEnd_2032744 1043774719543100113451587 := by
  unfold tailWord_2032744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070132273861563940544643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49426843031815418587392857 37070132273861563940544643)
  ·
    refine ⟨55605198410792345910816965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37070132273861563940544643 55605198410792345910816965)
    ·
      refine ⟨10425974702023564858278181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55605198410792345910816965 10425974702023564858278181)
      ·
        refine ⟨1954870256629418410927159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10425974702023564858278181 1954870256629418410927159)
        ·
          refine ⟨2932305384944127616390739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954870256629418410927159 2932305384944127616390739)
          ·
            refine ⟨4398458077416191424586109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932305384944127616390739 4398458077416191424586109)
            ·
              refine ⟨1649421779031071784219791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4398458077416191424586109 1649421779031071784219791)
              ·
                refine ⟨2474132668546607676329687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649421779031071784219791 2474132668546607676329687)
                ·
                  refine ⟨3711199002819911514494531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474132668546607676329687 3711199002819911514494531)
                  ·
                    refine ⟨5566798504229867271741797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3711199002819911514494531 5566798504229867271741797)
                    ·
                      refine ⟨1043774719543100113451587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5566798504229867271741797 1043774719543100113451587)
                      ·
                        rfl

theorem cell23_2032744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2032744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032744 prefixEnd_2032744 := by exact prefixLift 2032744
  have htrace : WordTrace (prefixWord ++ tailWord_2032744) baseStart_2032744 baseEnd_2032744 := by
    simpa [prefixWord, tailWord_2032744, baseEnd_2032744] using wordTrace_append hprefix tailTrace_2032744
  have hstable : (prefixWord ++ tailWord_2032744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032744).length < 2 ^ (prefixWord ++ tailWord_2032744).sum := by decide
  have hdescent : baseEnd_2032744 < baseStart_2032744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032760 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_2032760 : Nat := 118140960795 + 2032760 * 2 ^ 59
def prefixEnd_2032760 : Nat := 4983230072969 + 3 ^ 40 * 2032760 * 2
def baseEnd_2032760 : Nat := 1043782935233572050851513

theorem tailTrace_2032760 : CollatzResearch.WordTrace tailWord_2032760 prefixEnd_2032760 1043782935233572050851513 := by
  unfold tailWord_2032760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070424057832581306835867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49427232077110108409114489 37070424057832581306835867)
  ·
    refine ⟨55605636086748871960253801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37070424057832581306835867 55605636086748871960253801)
    ·
      refine ⟨41704227065061653970190351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55605636086748871960253801 41704227065061653970190351)
      ·
        refine ⟨62556340597592480955285527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41704227065061653970190351 62556340597592480955285527)
        ·
          refine ⟨93834510896388721432928291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62556340597592480955285527 93834510896388721432928291)
          ·
            refine ⟨140751766344583082149392437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93834510896388721432928291 140751766344583082149392437)
            ·
              refine ⟨13195478094804663951505541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140751766344583082149392437 13195478094804663951505541)
              ·
                refine ⟨2474152142775874490907289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13195478094804663951505541 2474152142775874490907289)
                ·
                  refine ⟨1855614107081905868180467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474152142775874490907289 1855614107081905868180467)
                  ·
                    refine ⟨2783421160622858802270701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855614107081905868180467 2783421160622858802270701)
                    ·
                      refine ⟨1043782935233572050851513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783421160622858802270701 1043782935233572050851513)
                      ·
                        rfl

theorem cell23_2032760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_2032760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032760 prefixEnd_2032760 := by exact prefixLift 2032760
  have htrace : WordTrace (prefixWord ++ tailWord_2032760) baseStart_2032760 baseEnd_2032760 := by
    simpa [prefixWord, tailWord_2032760, baseEnd_2032760] using wordTrace_append hprefix tailTrace_2032760
  have hstable : (prefixWord ++ tailWord_2032760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032760).length < 2 ^ (prefixWord ++ tailWord_2032760).sum := by decide
  have hdescent : baseEnd_2032760 < baseStart_2032760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032800 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2]
def baseStart_2032800 : Nat := 118140960795 + 2032800 * 2 ^ 59
def prefixEnd_2032800 : Nat := 4983230072969 + 3 ^ 40 * 2032800 * 2
def baseEnd_2032800 : Nat := 1043803474459751894351329

theorem tailTrace_2032800 : CollatzResearch.WordTrace tailWord_2032800 prefixEnd_2032800 1043803474459751894351329 := by
  unfold tailWord_2032800
  simp only [CollatzResearch.WordTrace]
  refine ⟨37071153517760124722563927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49428204690346832963418569 37071153517760124722563927)
  ·
    refine ⟨55606730276640187083845891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37071153517760124722563927 55606730276640187083845891)
    ·
      refine ⟨83410095414960280625768837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55606730276640187083845891 83410095414960280625768837)
      ·
        refine ⟨15639392890305052617331657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83410095414960280625768837 15639392890305052617331657)
        ·
          refine ⟨11729544667728789462998743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15639392890305052617331657 11729544667728789462998743)
          ·
            refine ⟨17594317001593184194498115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11729544667728789462998743 17594317001593184194498115)
            ·
              refine ⟨26391475502389776291747173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17594317001593184194498115 26391475502389776291747173)
              ·
                refine ⟨4948401656698083054702595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26391475502389776291747173 4948401656698083054702595)
                ·
                  refine ⟨7422602485047124582053893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948401656698083054702595 7422602485047124582053893)
                  ·
                    refine ⟨1391737965946335859135105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422602485047124582053893 1391737965946335859135105)
                    ·
                      refine ⟨1043803474459751894351329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391737965946335859135105 1043803474459751894351329)
                      ·
                        rfl

theorem cell23_2032800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_2032800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032800 prefixEnd_2032800 := by exact prefixLift 2032800
  have htrace : WordTrace (prefixWord ++ tailWord_2032800) baseStart_2032800 baseEnd_2032800 := by
    simpa [prefixWord, tailWord_2032800, baseEnd_2032800] using wordTrace_append hprefix tailTrace_2032800
  have hstable : (prefixWord ++ tailWord_2032800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032800).length < 2 ^ (prefixWord ++ tailWord_2032800).sum := by decide
  have hdescent : baseEnd_2032800 < baseStart_2032800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032804 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_2032804 : Nat := 118140960795 + 2032804 * 2 ^ 59
def prefixEnd_2032804 : Nat := 4983230072969 + 3 ^ 40 * 2032804 * 2
def baseEnd_2032804 : Nat := 1043805528382369878701311

theorem tailTrace_2032804 : CollatzResearch.WordTrace tailWord_2032804 prefixEnd_2032804 1043805528382369878701311 := by
  unfold tailWord_2032804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37071226463752879064136733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49428301951670505418848977 37071226463752879064136733)
  ·
    refine ⟨13901709923907329649051275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37071226463752879064136733 13901709923907329649051275)
    ·
      refine ⟨20852564885860994473576913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13901709923907329649051275 20852564885860994473576913)
      ·
        refine ⟨15639423664395745855182685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20852564885860994473576913 15639423664395745855182685)
        ·
          refine ⟨5864783874148404695693507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15639423664395745855182685 5864783874148404695693507)
          ·
            refine ⟨8797175811222607043540261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864783874148404695693507 8797175811222607043540261)
            ·
              refine ⟨1649470464604238820663799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8797175811222607043540261 1649470464604238820663799)
              ·
                refine ⟨2474205696906358230995699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649470464604238820663799 2474205696906358230995699)
                ·
                  refine ⟨3711308545359537346493549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474205696906358230995699 3711308545359537346493549)
                  ·
                    refine ⟨1391740704509826504935081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711308545359537346493549 1391740704509826504935081)
                    ·
                      refine ⟨1043805528382369878701311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391740704509826504935081 1043805528382369878701311)
                      ·
                        rfl

theorem cell23_2032804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_2032804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032804 prefixEnd_2032804 := by exact prefixLift 2032804
  have htrace : WordTrace (prefixWord ++ tailWord_2032804) baseStart_2032804 baseEnd_2032804 := by
    simpa [prefixWord, tailWord_2032804, baseEnd_2032804] using wordTrace_append hprefix tailTrace_2032804
  have hstable : (prefixWord ++ tailWord_2032804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032804).length < 2 ^ (prefixWord ++ tailWord_2032804).sum := by decide
  have hdescent : baseEnd_2032804 < baseStart_2032804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032810 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2032810 : Nat := 118140960795 + 2032810 * 2 ^ 59
def prefixEnd_2032810 : Nat := 4983230072969 + 3 ^ 40 * 2032810 * 2
def baseEnd_2032810 : Nat := 347936203088765618408761

theorem tailTrace_2032810 : CollatzResearch.WordTrace tailWord_2032810 prefixEnd_2032810 347936203088765618408761 := by
  unfold tailWord_2032810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535667941371005288247971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49428447843656014101994589 18535667941371005288247971)
  ·
    refine ⟨27803501912056507932371957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18535667941371005288247971 27803501912056507932371957)
    ·
      refine ⟨2606578304255297618659871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27803501912056507932371957 2606578304255297618659871)
      ·
        refine ⟨3909867456382946427989807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606578304255297618659871 3909867456382946427989807)
        ·
          refine ⟨5864801184574419641984711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909867456382946427989807 5864801184574419641984711)
          ·
            refine ⟨8797201776861629462977067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864801184574419641984711 8797201776861629462977067)
            ·
              refine ⟨13195802665292444194465601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8797201776861629462977067 13195802665292444194465601)
              ·
                refine ⟨9896851998969333145849201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13195802665292444194465601 9896851998969333145849201)
                ·
                  refine ⟨7422638999226999859386901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896851998969333145849201 7422638999226999859386901)
                  ·
                    refine ⟨347936203088765618408761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7422638999226999859386901 347936203088765618408761)
                    ·
                      rfl

theorem cell23_2032810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2032810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032810 prefixEnd_2032810 := by exact prefixLift 2032810
  have htrace : WordTrace (prefixWord ++ tailWord_2032810) baseStart_2032810 baseEnd_2032810 := by
    simpa [prefixWord, tailWord_2032810, baseEnd_2032810] using wordTrace_append hprefix tailTrace_2032810
  have hstable : (prefixWord ++ tailWord_2032810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032810).length < 2 ^ (prefixWord ++ tailWord_2032810).sum := by decide
  have hdescent : baseEnd_2032810 < baseStart_2032810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032816 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_2032816 : Nat := 118140960795 + 2032816 * 2 ^ 59
def prefixEnd_2032816 : Nat := 4983230072969 + 3 ^ 40 * 2032816 * 2
def baseEnd_2032816 : Nat := 1043811690150223831751255

theorem tailTrace_2032816 : CollatzResearch.WordTrace tailWord_2032816 prefixEnd_2032816 1043811690150223831751255 := by
  unfold tailWord_2032816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37071445301731142088855151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49428593735641522785140201 37071445301731142088855151)
  ·
    refine ⟨55607167952596713133282727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37071445301731142088855151 55607167952596713133282727)
    ·
      refine ⟨83410751928895069699924091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55607167952596713133282727 83410751928895069699924091)
      ·
        refine ⟨125116127893342604549886137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83410751928895069699924091 125116127893342604549886137)
        ·
          refine ⟨93837095920006953412414603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125116127893342604549886137 93837095920006953412414603)
          ·
            refine ⟨140755643880010430118621905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93837095920006953412414603 140755643880010430118621905)
            ·
              refine ⟨105566732910007822588966429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140755643880010430118621905 105566732910007822588966429)
              ·
                refine ⟨39587524841252933470862411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105566732910007822588966429 39587524841252933470862411)
                ·
                  refine ⟨59381287261879400206293617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39587524841252933470862411 59381287261879400206293617)
                  ·
                    refine ⟨44535965446409550154720213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59381287261879400206293617 44535965446409550154720213)
                    ·
                      refine ⟨1043811690150223831751255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44535965446409550154720213 1043811690150223831751255)
                      ·
                        rfl

theorem cell23_2032816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_2032816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032816 prefixEnd_2032816 := by exact prefixLift 2032816
  have htrace : WordTrace (prefixWord ++ tailWord_2032816) baseStart_2032816 baseEnd_2032816 := by
    simpa [prefixWord, tailWord_2032816, baseEnd_2032816] using wordTrace_append hprefix tailTrace_2032816
  have hstable : (prefixWord ++ tailWord_2032816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032816).length < 2 ^ (prefixWord ++ tailWord_2032816).sum := by decide
  have hdescent : baseEnd_2032816 < baseStart_2032816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032823 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 7]
def baseStart_2032823 : Nat := 118140960795 + 2032823 * 2 ^ 59
def prefixEnd_2032823 : Nat := 4983230072969 + 3 ^ 40 * 2032823 * 2
def baseEnd_2032823 : Nat := 115979476057200589373747

theorem tailTrace_2032823 : CollatzResearch.WordTrace tailWord_2032823 prefixEnd_2032823 115979476057200589373747 := by
  unfold tailWord_2032823
  simp only [CollatzResearch.WordTrace]
  refine ⟨74143145914436924373215123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49428763942957949582143415 74143145914436924373215123)
  ·
    refine ⟨111214718871655386559822685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74143145914436924373215123 111214718871655386559822685)
    ·
      refine ⟨41705519576870769959933507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111214718871655386559822685 41705519576870769959933507)
      ·
        refine ⟨62558279365306154939900261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41705519576870769959933507 62558279365306154939900261)
        ·
          refine ⟨11729677380994904051231299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62558279365306154939900261 11729677380994904051231299)
          ·
            refine ⟨17594516071492356076846949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11729677380994904051231299 17594516071492356076846949)
            ·
              refine ⟨3298971763404816764408803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17594516071492356076846949 3298971763404816764408803)
              ·
                refine ⟨4948457645107225146613205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298971763404816764408803 4948457645107225146613205)
                ·
                  refine ⟨115979476057200589373747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4948457645107225146613205 115979476057200589373747)
                  ·
                    rfl

theorem cell23_2032823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 7].length) (baseStart_2032823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032823 prefixEnd_2032823 := by exact prefixLift 2032823
  have htrace : WordTrace (prefixWord ++ tailWord_2032823) baseStart_2032823 baseEnd_2032823 := by
    simpa [prefixWord, tailWord_2032823, baseEnd_2032823] using wordTrace_append hprefix tailTrace_2032823
  have hstable : (prefixWord ++ tailWord_2032823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032823).length < 2 ^ (prefixWord ++ tailWord_2032823).sum := by decide
  have hdescent : baseEnd_2032823 < baseStart_2032823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032830 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2032830 : Nat := 118140960795 + 2032830 * 2 ^ 59
def prefixEnd_2032830 : Nat := 4983230072969 + 3 ^ 40 * 2032830 * 2
def baseEnd_2032830 : Nat := 1043818878879386776976191

theorem tailTrace_2032830 : CollatzResearch.WordTrace tailWord_2032830 prefixEnd_2032830 1043818878879386776976191 := by
  unfold tailWord_2032830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267925153176445571089993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49428934150274376379146629 9267925153176445571089993)
  ·
    refine ⟨6950943864882334178317495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9267925153176445571089993 6950943864882334178317495)
    ·
      refine ⟨10426415797323501267476243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950943864882334178317495 10426415797323501267476243)
      ·
        refine ⟨15639623695985251901214365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426415797323501267476243 15639623695985251901214365)
        ·
          refine ⟨5864858885994469462955387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15639623695985251901214365 5864858885994469462955387)
          ·
            refine ⟨8797288328991704194433081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864858885994469462955387 8797288328991704194433081)
            ·
              refine ⟨6597966246743778145824811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797288328991704194433081 6597966246743778145824811)
              ·
                refine ⟨9896949370115667218737217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597966246743778145824811 9896949370115667218737217)
                ·
                  refine ⟨7422712027586750414052913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896949370115667218737217 7422712027586750414052913)
                  ·
                    refine ⟨5567034020690062810539685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422712027586750414052913 5567034020690062810539685)
                    ·
                      refine ⟨1043818878879386776976191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5567034020690062810539685 1043818878879386776976191)
                      ·
                        rfl

theorem cell23_2032830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2032830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032830 prefixEnd_2032830 := by exact prefixLift 2032830
  have htrace : WordTrace (prefixWord ++ tailWord_2032830) baseStart_2032830 baseEnd_2032830 := by
    simpa [prefixWord, tailWord_2032830, baseEnd_2032830] using wordTrace_append hprefix tailTrace_2032830
  have hstable : (prefixWord ++ tailWord_2032830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032830).length < 2 ^ (prefixWord ++ tailWord_2032830).sum := by decide
  have hdescent : baseEnd_2032830 < baseStart_2032830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032890 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_2032890 : Nat := 118140960795 + 2032890 * 2 ^ 59
def prefixEnd_2032890 : Nat := 4983230072969 + 3 ^ 40 * 2032890 * 2
def baseEnd_2032890 : Nat := 1043849687718656542225915

theorem tailTrace_2032890 : CollatzResearch.WordTrace tailWord_2032890 prefixEnd_2032890 1043849687718656542225915 := by
  unfold tailWord_2032890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18536397401298548703976031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49430393070129463210602749 18536397401298548703976031)
  ·
    refine ⟨27804596101947823055964047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18536397401298548703976031 27804596101947823055964047)
    ·
      refine ⟨41706894152921734583946071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27804596101947823055964047 41706894152921734583946071)
      ·
        refine ⟨62560341229382601875919107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41706894152921734583946071 62560341229382601875919107)
        ·
          refine ⟨93840511844073902813878661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62560341229382601875919107 93840511844073902813878661)
          ·
            refine ⟨17595095970763856777602249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93840511844073902813878661 17595095970763856777602249)
            ·
              refine ⟨13196321978072892583201687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17595095970763856777602249 13196321978072892583201687)
              ·
                refine ⟨19794482967109338874802531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13196321978072892583201687 19794482967109338874802531)
                ·
                  refine ⟨29691724450664008312203797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19794482967109338874802531 29691724450664008312203797)
                  ·
                    refine ⟨1391799583624875389634553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29691724450664008312203797 1391799583624875389634553)
                    ·
                      refine ⟨1043849687718656542225915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391799583624875389634553 1043849687718656542225915)
                      ·
                        rfl

theorem cell23_2032890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_2032890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032890 prefixEnd_2032890 := by exact prefixLift 2032890
  have htrace : WordTrace (prefixWord ++ tailWord_2032890) baseStart_2032890 baseEnd_2032890 := by
    simpa [prefixWord, tailWord_2032890, baseEnd_2032890] using wordTrace_append hprefix tailTrace_2032890
  have hstable : (prefixWord ++ tailWord_2032890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032890).length < 2 ^ (prefixWord ++ tailWord_2032890).sum := by decide
  have hdescent : baseEnd_2032890 < baseStart_2032890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032917 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2032917 : Nat := 118140960795 + 2032917 * 2 ^ 59
def prefixEnd_2032917 : Nat := 4983230072969 + 3 ^ 40 * 2032917 * 2
def baseEnd_2032917 : Nat := 347954517232109312196097

theorem tailTrace_2032917 : CollatzResearch.WordTrace tailWord_2032917 prefixEnd_2032917 347954517232109312196097 := by
  unfold tailWord_2032917
  simp only [CollatzResearch.WordTrace]
  refine ⟨74146574376096378427137005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49431049584064252284758003 74146574376096378427137005)
  ·
    refine ⟨27804965391036141910176377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74146574376096378427137005 27804965391036141910176377)
    ·
      refine ⟨20853724043277106432632283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27804965391036141910176377 20853724043277106432632283)
      ·
        refine ⟨31280586064915659648948425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20853724043277106432632283 31280586064915659648948425)
        ·
          refine ⟨23460439548686744736711319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31280586064915659648948425 23460439548686744736711319)
          ·
            refine ⟨35190659323030117105066979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23460439548686744736711319 35190659323030117105066979)
            ·
              refine ⟨52785988984545175657600469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35190659323030117105066979 52785988984545175657600469)
              ·
                refine ⟨1237171616825277554475011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52785988984545175657600469 1237171616825277554475011)
                ·
                  refine ⟨1855757425237916331712517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237171616825277554475011 1855757425237916331712517)
                  ·
                    refine ⟨347954517232109312196097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855757425237916331712517 347954517232109312196097)
                    ·
                      rfl

theorem cell23_2032917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2032917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032917 prefixEnd_2032917 := by exact prefixLift 2032917
  have htrace : WordTrace (prefixWord ++ tailWord_2032917) baseStart_2032917 baseEnd_2032917 := by
    simpa [prefixWord, tailWord_2032917, baseEnd_2032917] using wordTrace_append hprefix tailTrace_2032917
  have hstable : (prefixWord ++ tailWord_2032917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032917).length < 2 ^ (prefixWord ++ tailWord_2032917).sum := by decide
  have hdescent : baseEnd_2032917 < baseStart_2032917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032960 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_2032960 : Nat := 118140960795 + 2032960 * 2 ^ 59
def prefixEnd_2032960 : Nat := 4983230072969 + 3 ^ 40 * 2032960 * 2
def baseEnd_2032960 : Nat := 347961877121490422783531

theorem tailTrace_2032960 : CollatzResearch.WordTrace tailWord_2032960 prefixEnd_2032960 347961877121490422783531 := by
  unfold tailWord_2032960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37074071357470298385476167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49432095143293731180634889 37074071357470298385476167)
  ·
    refine ⟨55611107036205447578214251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37074071357470298385476167 55611107036205447578214251)
    ·
      refine ⟨83416660554308171367321377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55611107036205447578214251 83416660554308171367321377)
      ·
        refine ⟨62562495415731128525491033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83416660554308171367321377 62562495415731128525491033)
        ·
          refine ⟨46921871561798346394118275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62562495415731128525491033 46921871561798346394118275)
          ·
            refine ⟨70382807342697519591177413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46921871561798346394118275 70382807342697519591177413)
            ·
              refine ⟨13196776376755784923345765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70382807342697519591177413 13196776376755784923345765)
              ·
                refine ⟨2474395570641709673127331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13196776376755784923345765 2474395570641709673127331)
                ·
                  refine ⟨3711593355962564509690997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474395570641709673127331 3711593355962564509690997)
                  ·
                    refine ⟨347961877121490422783531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3711593355962564509690997 347961877121490422783531)
                    ·
                      rfl

theorem cell23_2032960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_2032960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032960 prefixEnd_2032960 := by exact prefixLift 2032960
  have htrace : WordTrace (prefixWord ++ tailWord_2032960) baseStart_2032960 baseEnd_2032960 := by
    simpa [prefixWord, tailWord_2032960, baseEnd_2032960] using wordTrace_append hprefix tailTrace_2032960
  have hstable : (prefixWord ++ tailWord_2032960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032960).length < 2 ^ (prefixWord ++ tailWord_2032960).sum := by decide
  have hdescent : baseEnd_2032960 < baseStart_2032960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2032967 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_2032967 : Nat := 118140960795 + 2032967 * 2 ^ 59
def prefixEnd_2032967 : Nat := 4983230072969 + 3 ^ 40 * 2032967 * 2
def baseEnd_2032967 : Nat := 1043889225729052740963061

theorem tailTrace_2032967 : CollatzResearch.WordTrace tailWord_2032967 prefixEnd_2032967 1043889225729052740963061 := by
  unfold tailWord_2032967
  simp only [CollatzResearch.WordTrace]
  refine ⟨74148398025915236966457155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49432265350610157977638103 74148398025915236966457155)
  ·
    refine ⟨111222597038872855449685733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74148398025915236966457155 111222597038872855449685733)
    ·
      refine ⟨20854236944788660396816075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111222597038872855449685733 20854236944788660396816075)
      ·
        refine ⟨31281355417182990595224113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20854236944788660396816075 31281355417182990595224113)
        ·
          refine ⟨23461016562887242946418085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31281355417182990595224113 23461016562887242946418085)
          ·
            refine ⟨4398940605541358052453391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23461016562887242946418085 4398940605541358052453391)
            ·
              refine ⟨6598410908312037078680087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398940605541358052453391 6598410908312037078680087)
              ·
                refine ⟨9897616362468055618020131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598410908312037078680087 9897616362468055618020131)
                ·
                  refine ⟨14846424543702083427030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897616362468055618020131 14846424543702083427030197)
                  ·
                    refine ⟨1391852300972070321284081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14846424543702083427030197 1391852300972070321284081)
                    ·
                      refine ⟨1043889225729052740963061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391852300972070321284081 1043889225729052740963061)
                      ·
                        rfl

theorem cell23_2032967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_2032967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2032967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2032967 prefixEnd_2032967 := by exact prefixLift 2032967
  have htrace : WordTrace (prefixWord ++ tailWord_2032967) baseStart_2032967 baseEnd_2032967 := by
    simpa [prefixWord, tailWord_2032967, baseEnd_2032967] using wordTrace_append hprefix tailTrace_2032967
  have hstable : (prefixWord ++ tailWord_2032967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2032967).length < 2 ^ (prefixWord ++ tailWord_2032967).sum := by decide
  have hdescent : baseEnd_2032967 < baseStart_2032967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2032967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033010 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2033010 : Nat := 118140960795 + 2033010 * 2 ^ 59
def prefixEnd_2033010 : Nat := 4983230072969 + 3 ^ 40 * 2033010 * 2
def baseEnd_2033010 : Nat := 1043911305397196072725363

theorem tailTrace_2033010 : CollatzResearch.WordTrace tailWord_2033010 prefixEnd_2033010 1043911305397196072725363 := by
  unfold tailWord_2033010
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537491591189863827568121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49433310909839636873514989 18537491591189863827568121)
  ·
    refine ⟨13903118693392397870676091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18537491591189863827568121 13903118693392397870676091)
    ·
      refine ⟨20854678040088596806014137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13903118693392397870676091 20854678040088596806014137)
      ·
        refine ⟨15641008530066447604510603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20854678040088596806014137 15641008530066447604510603)
        ·
          refine ⟨23461512795099671406765905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15641008530066447604510603 23461512795099671406765905)
          ·
            refine ⟨17596134596324753555074429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23461512795099671406765905 17596134596324753555074429)
            ·
              refine ⟨6598550473621782583152911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17596134596324753555074429 6598550473621782583152911)
              ·
                refine ⟨9897825710432673874729367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598550473621782583152911 9897825710432673874729367)
                ·
                  refine ⟨14846738565649010812094051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897825710432673874729367 14846738565649010812094051)
                  ·
                    refine ⟨22270107848473516218141077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14846738565649010812094051 22270107848473516218141077)
                    ·
                      refine ⟨1043911305397196072725363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22270107848473516218141077 1043911305397196072725363)
                      ·
                        rfl

theorem cell23_2033010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2033010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033010 prefixEnd_2033010 := by exact prefixLift 2033010
  have htrace : WordTrace (prefixWord ++ tailWord_2033010) baseStart_2033010 baseEnd_2033010 := by
    simpa [prefixWord, tailWord_2033010, baseEnd_2033010] using wordTrace_append hprefix tailTrace_2033010
  have hstable : (prefixWord ++ tailWord_2033010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033010).length < 2 ^ (prefixWord ++ tailWord_2033010).sum := by decide
  have hdescent : baseEnd_2033010 < baseStart_2033010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033017 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_2033017 : Nat := 118140960795 + 2033017 * 2 ^ 59
def prefixEnd_2033017 : Nat := 4983230072969 + 3 ^ 40 * 2033017 * 2
def baseEnd_2033017 : Nat := 1043914899761777545337831

theorem tailTrace_2033017 : CollatzResearch.WordTrace tailWord_2033017 prefixEnd_2033017 1043914899761777545337831 := by
  unfold tailWord_2033017
  simp only [CollatzResearch.WordTrace]
  refine ⟨74150221675734095505777305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49433481117156063670518203 74150221675734095505777305)
  ·
    refine ⟨55612666256800571629332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74150221675734095505777305 55612666256800571629332979)
    ·
      refine ⟨83418999385200857443999469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55612666256800571629332979 83418999385200857443999469)
      ·
        refine ⟨31282124769450321541499801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83418999385200857443999469 31282124769450321541499801)
        ·
          refine ⟨23461593577087741156124851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31282124769450321541499801 23461593577087741156124851)
          ·
            refine ⟨35192390365631611734187277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23461593577087741156124851 35192390365631611734187277)
            ·
              refine ⟨13197146387111854400320229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35192390365631611734187277 13197146387111854400320229)
              ·
                refine ⟨2474464947583472700060043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13197146387111854400320229 2474464947583472700060043)
                ·
                  refine ⟨3711697421375209050090065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474464947583472700060043 3711697421375209050090065)
                  ·
                    refine ⟨2783773066031406787567549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3711697421375209050090065 2783773066031406787567549)
                    ·
                      refine ⟨1043914899761777545337831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783773066031406787567549 1043914899761777545337831)
                      ·
                        rfl

theorem cell23_2033017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_2033017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033017 prefixEnd_2033017 := by exact prefixLift 2033017
  have htrace : WordTrace (prefixWord ++ tailWord_2033017) baseStart_2033017 baseEnd_2033017 := by
    simpa [prefixWord, tailWord_2033017, baseEnd_2033017] using wordTrace_append hprefix tailTrace_2033017
  have hstable : (prefixWord ++ tailWord_2033017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033017).length < 2 ^ (prefixWord ++ tailWord_2033017).sum := by decide
  have hdescent : baseEnd_2033017 < baseStart_2033017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033025 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2033025 : Nat := 118140960795 + 2033025 * 2 ^ 59
def prefixEnd_2033025 : Nat := 4983230072969 + 3 ^ 40 * 2033025 * 2
def baseEnd_2033025 : Nat := 1043919007607013514037795

theorem tailTrace_2033025 : CollatzResearch.WordTrace tailWord_2033025 prefixEnd_2033025 1043919007607013514037795 := by
  unfold tailWord_2033025
  simp only [CollatzResearch.WordTrace]
  refine ⟨74150513459705112872068529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49433675639803408581379019 74150513459705112872068529)
  ·
    refine ⟨55612885094778834654051397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74150513459705112872068529 55612885094778834654051397)
    ·
      refine ⟨10427415955271031497634637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55612885094778834654051397 10427415955271031497634637)
      ·
        refine ⟨3910280983226636811612989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10427415955271031497634637 3910280983226636811612989)
        ·
          refine ⟨1466355368709988804354871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3910280983226636811612989 1466355368709988804354871)
          ·
            refine ⟨2199533053064983206532307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466355368709988804354871 2199533053064983206532307)
            ·
              refine ⟨3299299579597474809798461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199533053064983206532307 3299299579597474809798461)
              ·
                refine ⟨1237237342349053053674423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3299299579597474809798461 1237237342349053053674423)
                ·
                  refine ⟨1855856013523579580511635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237237342349053053674423 1855856013523579580511635)
                  ·
                    refine ⟨2783784020285369370767453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855856013523579580511635 2783784020285369370767453)
                    ·
                      refine ⟨1043919007607013514037795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2783784020285369370767453 1043919007607013514037795)
                      ·
                        rfl

theorem cell23_2033025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2033025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033025 prefixEnd_2033025 := by exact prefixLift 2033025
  have htrace : WordTrace (prefixWord ++ tailWord_2033025) baseStart_2033025 baseEnd_2033025 := by
    simpa [prefixWord, tailWord_2033025, baseEnd_2033025] using wordTrace_append hprefix tailTrace_2033025
  have hstable : (prefixWord ++ tailWord_2033025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033025).length < 2 ^ (prefixWord ++ tailWord_2033025).sum := by decide
  have hdescent : baseEnd_2033025 < baseStart_2033025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033048 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2033048 : Nat := 118140960795 + 2033048 * 2 ^ 59
def prefixEnd_2033048 : Nat := 4983230072969 + 3 ^ 40 * 2033048 * 2
def baseEnd_2033048 : Nat := 1043930817662066924050189

theorem tailTrace_2033048 : CollatzResearch.WordTrace tailWord_2033048 prefixEnd_2033048 1043930817662066924050189 := by
  unfold tailWord_2033048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075676169310893900077899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49434234892414525200103865 37075676169310893900077899)
  ·
    refine ⟨55613514253966340850116849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37075676169310893900077899 55613514253966340850116849)
    ·
      refine ⟨41710135690474755637587637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55613514253966340850116849 41710135690474755637587637)
      ·
        refine ⟨3910325220982008341023841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41710135690474755637587637 3910325220982008341023841)
        ·
          refine ⟨2932743915736506255767881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910325220982008341023841 2932743915736506255767881)
          ·
            refine ⟨2199557936802379691825911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2932743915736506255767881 2199557936802379691825911)
            ·
              refine ⟨3299336905203569537738867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199557936802379691825911 3299336905203569537738867)
              ·
                refine ⟨4949005357805354306608301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299336905203569537738867 4949005357805354306608301)
                ·
                  refine ⟨1855877009177007864978113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4949005357805354306608301 1855877009177007864978113)
                  ·
                    refine ⟨1391907756882755898733585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1855877009177007864978113 1391907756882755898733585)
                    ·
                      refine ⟨1043930817662066924050189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391907756882755898733585 1043930817662066924050189)
                      ·
                        rfl

theorem cell23_2033048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2033048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033048 prefixEnd_2033048 := by exact prefixLift 2033048
  have htrace : WordTrace (prefixWord ++ tailWord_2033048) baseStart_2033048 baseEnd_2033048 := by
    simpa [prefixWord, tailWord_2033048, baseEnd_2033048] using wordTrace_append hprefix tailTrace_2033048
  have hstable : (prefixWord ++ tailWord_2033048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033048).length < 2 ^ (prefixWord ++ tailWord_2033048).sum := by decide
  have hdescent : baseEnd_2033048 < baseStart_2033048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033050 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_2033050 : Nat := 118140960795 + 2033050 * 2 ^ 59
def prefixEnd_2033050 : Nat := 4983230072969 + 3 ^ 40 * 2033050 * 2
def baseEnd_2033050 : Nat := 347977281541125305408393

theorem tailTrace_2033050 : CollatzResearch.WordTrace tailWord_2033050 prefixEnd_2033050 347977281541125305408393 := by
  unfold tailWord_2033050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537856321153635535432151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49434283523076361427819069 18537856321153635535432151)
  ·
    refine ⟨27806784481730453303148227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18537856321153635535432151 27806784481730453303148227)
    ·
      refine ⟨41710176722595679954722341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27806784481730453303148227 41710176722595679954722341)
      ·
        refine ⟨7820658135486689991510439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41710176722595679954722341 7820658135486689991510439)
        ·
          refine ⟨11730987203230034987265659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820658135486689991510439 11730987203230034987265659)
          ·
            refine ⟨17596480804845052480898489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730987203230034987265659 17596480804845052480898489)
            ·
              refine ⟨13197360603633789360673867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17596480804845052480898489 13197360603633789360673867)
              ·
                refine ⟨19796040905450684041010801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197360603633789360673867 19796040905450684041010801)
                ·
                  refine ⟨14847030679088013030758101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19796040905450684041010801 14847030679088013030758101)
                  ·
                    refine ⟨347977281541125305408393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14847030679088013030758101 347977281541125305408393)
                    ·
                      rfl

theorem cell23_2033050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_2033050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033050 prefixEnd_2033050 := by exact prefixLift 2033050
  have htrace : WordTrace (prefixWord ++ tailWord_2033050) baseStart_2033050 baseEnd_2033050 := by
    simpa [prefixWord, tailWord_2033050, baseEnd_2033050] using wordTrace_append hprefix tailTrace_2033050
  have hstable : (prefixWord ++ tailWord_2033050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033050).length < 2 ^ (prefixWord ++ tailWord_2033050).sum := by decide
  have hdescent : baseEnd_2033050 < baseStart_2033050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033054 : List Nat := [4, 3, 1, 2, 2, 1, 2, 8]
def baseStart_2033054 : Nat := 118140960795 + 2033054 * 2 ^ 59
def prefixEnd_2033054 : Nat := 4983230072969 + 3 ^ 40 * 2033054 * 2
def baseEnd_2033054 : Nat := 38664218464666440762043

theorem tailTrace_2033054 : CollatzResearch.WordTrace tailWord_2033054 prefixEnd_2033054 38664218464666440762043 := by
  unfold tailWord_2033054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268946397075006353109277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49434380784400033883249477 9268946397075006353109277)
  ·
    refine ⟨3475854898903127382415979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9268946397075006353109277 3475854898903127382415979)
    ·
      refine ⟨5213782348354691073623969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475854898903127382415979 5213782348354691073623969)
      ·
        refine ⟨3910336761266018305217977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5213782348354691073623969 3910336761266018305217977)
        ·
          refine ⟨2932752570949513728913483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910336761266018305217977 2932752570949513728913483)
          ·
            refine ⟨4399128856424270593370225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932752570949513728913483 4399128856424270593370225)
            ·
              refine ⟨3299346642318202945027669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399128856424270593370225 3299346642318202945027669)
              ·
                refine ⟨38664218464666440762043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3299346642318202945027669 38664218464666440762043)
                ·
                  rfl

theorem cell23_2033054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_2033054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033054 prefixEnd_2033054 := by exact prefixLift 2033054
  have htrace : WordTrace (prefixWord ++ tailWord_2033054) baseStart_2033054 baseEnd_2033054 := by
    simpa [prefixWord, tailWord_2033054, baseEnd_2033054] using wordTrace_append hprefix tailTrace_2033054
  have hstable : (prefixWord ++ tailWord_2033054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033054).length < 2 ^ (prefixWord ++ tailWord_2033054).sum := by decide
  have hdescent : baseEnd_2033054 < baseStart_2033054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033074 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_2033074 : Nat := 118140960795 + 2033074 * 2 ^ 59
def prefixEnd_2033074 : Nat := 4983230072969 + 3 ^ 40 * 2033074 * 2
def baseEnd_2033074 : Nat := 1043944168159083822325069

theorem tailTrace_2033074 : CollatzResearch.WordTrace tailWord_2033074 prefixEnd_2033074 1043944168159083822325069 := by
  unfold tailWord_2033074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18538075159131898560150569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49434867091018396160401517 18538075159131898560150569)
  ·
    refine ⟨13903556369348923920112927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18538075159131898560150569 13903556369348923920112927)
    ·
      refine ⟨20855334554023385880169391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13903556369348923920112927 20855334554023385880169391)
      ·
        refine ⟨31283001831035078820254087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20855334554023385880169391 31283001831035078820254087)
        ·
          refine ⟨46924502746552618230381131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31283001831035078820254087 46924502746552618230381131)
          ·
            refine ⟨70386754119828927345571697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46924502746552618230381131 70386754119828927345571697)
            ·
              refine ⟨52790065589871695509178773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70386754119828927345571697 52790065589871695509178773)
              ·
                refine ⟨2474534324525235726992755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52790065589871695509178773 2474534324525235726992755)
                ·
                  refine ⟨3711801486787853590489133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474534324525235726992755 3711801486787853590489133)
                  ·
                    refine ⟨1391925557545445096433425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711801486787853590489133 1391925557545445096433425)
                    ·
                      refine ⟨1043944168159083822325069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391925557545445096433425 1043944168159083822325069)
                      ·
                        rfl

theorem cell23_2033074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_2033074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033074 prefixEnd_2033074 := by exact prefixLift 2033074
  have htrace : WordTrace (prefixWord ++ tailWord_2033074) baseStart_2033074 baseEnd_2033074 := by
    simpa [prefixWord, tailWord_2033074, baseEnd_2033074] using wordTrace_append hprefix tailTrace_2033074
  have hstable : (prefixWord ++ tailWord_2033074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033074).length < 2 ^ (prefixWord ++ tailWord_2033074).sum := by decide
  have hdescent : baseEnd_2033074 < baseStart_2033074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033117 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2033117 : Nat := 118140960795 + 2033117 * 2 ^ 59
def prefixEnd_2033117 : Nat := 4983230072969 + 3 ^ 40 * 2033117 * 2
def baseEnd_2033117 : Nat := 1043966247827227154087371

theorem tailTrace_2033117 : CollatzResearch.WordTrace tailWord_2033117 prefixEnd_2033117 1043966247827227154087371 := by
  unfold tailWord_2033117
  simp only [CollatzResearch.WordTrace]
  refine ⟨74153868975371812584417605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49435912650247875056278403 74153868975371812584417605)
  ·
    refine ⟨13903850432882214859578301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74153868975371812584417605 13903850432882214859578301)
    ·
      refine ⟨5213943912330830572341863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13903850432882214859578301 5213943912330830572341863)
      ·
        refine ⟨7820915868496245858512795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213943912330830572341863 7820915868496245858512795)
        ·
          refine ⟨11731373802744368787769193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820915868496245858512795 11731373802744368787769193)
          ·
            refine ⟨8798530352058276590826895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731373802744368787769193 8798530352058276590826895)
            ·
              refine ⟨13197795528087414886240343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798530352058276590826895 13197795528087414886240343)
              ·
                refine ⟨19796693292131122329360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197795528087414886240343 19796693292131122329360515)
                ·
                  refine ⟨29695039938196683494040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19796693292131122329360515 29695039938196683494040773)
                  ·
                    refine ⟨5567819988411878155132645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29695039938196683494040773 5567819988411878155132645)
                    ·
                      refine ⟨1043966247827227154087371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5567819988411878155132645 1043966247827227154087371)
                      ·
                        rfl

theorem cell23_2033117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2033117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033117 prefixEnd_2033117 := by exact prefixLift 2033117
  have htrace : WordTrace (prefixWord ++ tailWord_2033117) baseStart_2033117 baseEnd_2033117 := by
    simpa [prefixWord, tailWord_2033117, baseEnd_2033117] using wordTrace_append hprefix tailTrace_2033117
  have hstable : (prefixWord ++ tailWord_2033117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033117).length < 2 ^ (prefixWord ++ tailWord_2033117).sum := by decide
  have hdescent : baseEnd_2033117 < baseStart_2033117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033121 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_2033121 : Nat := 118140960795 + 2033121 * 2 ^ 59
def prefixEnd_2033121 : Nat := 4983230072969 + 3 ^ 40 * 2033121 * 2
def baseEnd_2033121 : Nat := 1043968301749845138437353

theorem tailTrace_2033121 : CollatzResearch.WordTrace tailWord_2033121 prefixEnd_2033121 1043968301749845138437353 := by
  unfold tailWord_2033121
  simp only [CollatzResearch.WordTrace]
  refine ⟨74154014867357321267563217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49436009911571547511708811 74154014867357321267563217)
  ·
    refine ⟨55615511150517990950672413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74154014867357321267563217 55615511150517990950672413)
    ·
      refine ⟨20855816681444246606502155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55615511150517990950672413 20855816681444246606502155)
      ·
        refine ⟨31283725022166369909753233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20855816681444246606502155 31283725022166369909753233)
        ·
          refine ⟨23462793766624777432314925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31283725022166369909753233 23462793766624777432314925)
          ·
            refine ⟨8798547662484291537118097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23462793766624777432314925 8798547662484291537118097)
            ·
              refine ⟨6598910746863218652838573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8798547662484291537118097 6598910746863218652838573)
              ·
                refine ⟨2474591530073706994814465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6598910746863218652838573 2474591530073706994814465)
                ·
                  refine ⟨1855943647555280246110849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474591530073706994814465 1855943647555280246110849)
                  ·
                    refine ⟨1391957735666460184583137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1855943647555280246110849 1391957735666460184583137)
                    ·
                      refine ⟨1043968301749845138437353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391957735666460184583137 1043968301749845138437353)
                      ·
                        rfl

theorem cell23_2033121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_2033121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033121 prefixEnd_2033121 := by exact prefixLift 2033121
  have htrace : WordTrace (prefixWord ++ tailWord_2033121) baseStart_2033121 baseEnd_2033121 := by
    simpa [prefixWord, tailWord_2033121, baseEnd_2033121] using wordTrace_append hprefix tailTrace_2033121
  have hstable : (prefixWord ++ tailWord_2033121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033121).length < 2 ^ (prefixWord ++ tailWord_2033121).sum := by decide
  have hdescent : baseEnd_2033121 < baseStart_2033121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033127 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 7]
def baseStart_2033127 : Nat := 118140960795 + 2033127 * 2 ^ 59
def prefixEnd_2033127 : Nat := 4983230072969 + 3 ^ 40 * 2033127 * 2
def baseEnd_2033127 : Nat := 115996820292641346106925

theorem tailTrace_2033127 : CollatzResearch.WordTrace tailWord_2033127 prefixEnd_2033127 115996820292641346106925 := by
  unfold tailWord_2033127
  simp only [CollatzResearch.WordTrace]
  refine ⟨74154233705335584292281635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49436155803557056194854423 74154233705335584292281635)
  ·
    refine ⟨111231350558003376438422453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74154233705335584292281635 111231350558003376438422453)
    ·
      refine ⟨10427939114812816541102105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111231350558003376438422453 10427939114812816541102105)
      ·
        refine ⟨7820954336109612405826579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10427939114812816541102105 7820954336109612405826579)
        ·
          refine ⟨11731431504164418608739869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820954336109612405826579 11731431504164418608739869)
          ·
            refine ⟨4399286814061656978277451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11731431504164418608739869 4399286814061656978277451)
            ·
              refine ⟨6598930221092485467416177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399286814061656978277451 6598930221092485467416177)
              ·
                refine ⟨4949197665819364100562133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6598930221092485467416177 4949197665819364100562133)
                ·
                  refine ⟨115996820292641346106925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4949197665819364100562133 115996820292641346106925)
                  ·
                    rfl

theorem cell23_2033127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 7].length) (baseStart_2033127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033127 prefixEnd_2033127 := by exact prefixLift 2033127
  have htrace : WordTrace (prefixWord ++ tailWord_2033127) baseStart_2033127 baseEnd_2033127 := by
    simpa [prefixWord, tailWord_2033127, baseEnd_2033127] using wordTrace_append hprefix tailTrace_2033127
  have hstable : (prefixWord ++ tailWord_2033127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033127).length < 2 ^ (prefixWord ++ tailWord_2033127).sum := by decide
  have hdescent : baseEnd_2033127 < baseStart_2033127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033144 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 5]
def baseStart_2033144 : Nat := 118140960795 + 2033144 * 2 ^ 59
def prefixEnd_2033144 : Nat := 4983230072969 + 3 ^ 40 * 2033144 * 2
def baseEnd_2033144 : Nat := 115997790200544283161083

theorem tailTrace_2033144 : CollatzResearch.WordTrace tailWord_2033144 prefixEnd_2033144 115997790200544283161083 := by
  unfold tailWord_2033144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37077426873136998097825243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49436569164182664130433657 37077426873136998097825243)
  ·
    refine ⟨55616140309705497146737865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37077426873136998097825243 55616140309705497146737865)
    ·
      refine ⟨41712105232279122860053399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55616140309705497146737865 41712105232279122860053399)
      ·
        refine ⟨62568157848418684290080099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41712105232279122860053399 62568157848418684290080099)
        ·
          refine ⟨93852236772628026435120149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62568157848418684290080099 93852236772628026435120149)
          ·
            refine ⟨4399323598716938739146257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93852236772628026435120149 4399323598716938739146257)
            ·
              refine ⟨3299492699037704054359693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399323598716938739146257 3299492699037704054359693)
              ·
                refine ⟨1237309762139139020384885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3299492699037704054359693 1237309762139139020384885)
                ·
                  refine ⟨115997790200544283161083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1237309762139139020384885 115997790200544283161083)
                  ·
                    rfl

theorem cell23_2033144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 5].length) (baseStart_2033144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033144 prefixEnd_2033144 := by exact prefixLift 2033144
  have htrace : WordTrace (prefixWord ++ tailWord_2033144) baseStart_2033144 baseEnd_2033144 := by
    simpa [prefixWord, tailWord_2033144, baseEnd_2033144] using wordTrace_append hprefix tailTrace_2033144
  have hstable : (prefixWord ++ tailWord_2033144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033144).length < 2 ^ (prefixWord ++ tailWord_2033144).sum := by decide
  have hdescent : baseEnd_2033144 < baseStart_2033144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033147 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 5, 2]
def baseStart_2033147 : Nat := 118140960795 + 2033147 * 2 ^ 59
def prefixEnd_2033147 : Nat := 4983230072969 + 3 ^ 40 * 2033147 * 2
def baseEnd_2033147 : Nat := 1043981652246862036712233

theorem tailTrace_2033147 : CollatzResearch.WordTrace tailWord_2033147 prefixEnd_2033147 1043981652246862036712233 := by
  unfold tailWord_2033147
  simp only [CollatzResearch.WordTrace]
  refine ⟨74154963165263127708009695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49436642110175418472006463 74154963165263127708009695)
  ·
    refine ⟨111232444747894691562014543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74154963165263127708009695 111232444747894691562014543)
    ·
      refine ⟨166848667121842037343021815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111232444747894691562014543 166848667121842037343021815)
      ·
        refine ⟨250273000682763056014532723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166848667121842037343021815 250273000682763056014532723)
        ·
          refine ⟨375409501024144584021799085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250273000682763056014532723 375409501024144584021799085)
          ·
            refine ⟨140778562884054219008174657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375409501024144584021799085 140778562884054219008174657)
            ·
              refine ⟨105583922163040664256130993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140778562884054219008174657 105583922163040664256130993)
              ·
                refine ⟨79187941622280498192098245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105583922163040664256130993 79187941622280498192098245)
                ·
                  refine ⟨14847739054177593411018421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79187941622280498192098245 14847739054177593411018421)
                  ·
                    refine ⟨1391975536329149382282977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14847739054177593411018421 1391975536329149382282977)
                    ·
                      refine ⟨1043981652246862036712233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391975536329149382282977 1043981652246862036712233)
                      ·
                        rfl

theorem cell23_2033147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5, 2].length) (baseStart_2033147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033147 prefixEnd_2033147 := by exact prefixLift 2033147
  have htrace : WordTrace (prefixWord ++ tailWord_2033147) baseStart_2033147 baseEnd_2033147 := by
    simpa [prefixWord, tailWord_2033147, baseEnd_2033147] using wordTrace_append hprefix tailTrace_2033147
  have hstable : (prefixWord ++ tailWord_2033147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033147).length < 2 ^ (prefixWord ++ tailWord_2033147).sum := by decide
  have hdescent : baseEnd_2033147 < baseStart_2033147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033172 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2033172 : Nat := 118140960795 + 2033172 * 2 ^ 59
def prefixEnd_2033172 : Nat := 4983230072969 + 3 ^ 40 * 2033172 * 2
def baseEnd_2033172 : Nat := 1043994489263224438899619

theorem tailTrace_2033172 : CollatzResearch.WordTrace tailWord_2033172 prefixEnd_2033172 1043994489263224438899619 := by
  unfold tailWord_2033172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37077937495086278488834885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49437249993448371318446513 37077937495086278488834885)
  ·
    refine ⟨6952113280328677216656541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37077937495086278488834885 6952113280328677216656541)
    ·
      refine ⟨2607042480123253956246203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6952113280328677216656541 2607042480123253956246203)
      ·
        refine ⟨3910563720184880934369305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607042480123253956246203 3910563720184880934369305)
        ·
          refine ⟨2932922790138660700776979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910563720184880934369305 2932922790138660700776979)
          ·
            refine ⟨4399384185207991051165469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932922790138660700776979 4399384185207991051165469)
            ·
              refine ⟨1649769069452996644187051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4399384185207991051165469 1649769069452996644187051)
              ·
                refine ⟨2474653604179494966280577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649769069452996644187051 2474653604179494966280577)
                ·
                  refine ⟨1855990203134621224710433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474653604179494966280577 1855990203134621224710433)
                  ·
                    refine ⟨1391992652350965918532825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1855990203134621224710433 1391992652350965918532825)
                    ·
                      refine ⟨1043994489263224438899619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1391992652350965918532825 1043994489263224438899619)
                      ·
                        rfl

theorem cell23_2033172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2033172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033172 prefixEnd_2033172 := by exact prefixLift 2033172
  have htrace : WordTrace (prefixWord ++ tailWord_2033172) baseStart_2033172 baseEnd_2033172 := by
    simpa [prefixWord, tailWord_2033172, baseEnd_2033172] using wordTrace_append hprefix tailTrace_2033172
  have hstable : (prefixWord ++ tailWord_2033172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033172).length < 2 ^ (prefixWord ++ tailWord_2033172).sum := by decide
  have hdescent : baseEnd_2033172 < baseStart_2033172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033194 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2033194 : Nat := 118140960795 + 2033194 * 2 ^ 59
def prefixEnd_2033194 : Nat := 4983230072969 + 3 ^ 40 * 2033194 * 2
def baseEnd_2033194 : Nat := 1044005785837623352824517

theorem tailTrace_2033194 : CollatzResearch.WordTrace tailWord_2033194 prefixEnd_2033194 1044005785837623352824517 := by
  unfold tailWord_2033194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539169349023213683742659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49437784930728569823313757 18539169349023213683742659)
  ·
    refine ⟨27808754023534820525613989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18539169349023213683742659 27808754023534820525613989)
    ·
      refine ⟨5214141379412778848552623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27808754023534820525613989 5214141379412778848552623)
      ·
        refine ⟨7821212069119168272828935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214141379412778848552623 7821212069119168272828935)
        ·
          refine ⟨11731818103678752409243403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821212069119168272828935 11731818103678752409243403)
          ·
            refine ⟨17597727155518128613865105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11731818103678752409243403 17597727155518128613865105)
            ·
              refine ⟨13198295366638596460398829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17597727155518128613865105 13198295366638596460398829)
              ·
                refine ⟨4949360762489473672649561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13198295366638596460398829 4949360762489473672649561)
                ·
                  refine ⟨3712020571867105254487171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4949360762489473672649561 3712020571867105254487171)
                  ·
                    refine ⟨5568030857800657881730757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712020571867105254487171 5568030857800657881730757)
                    ·
                      refine ⟨1044005785837623352824517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5568030857800657881730757 1044005785837623352824517)
                      ·
                        rfl

theorem cell23_2033194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2033194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033194 prefixEnd_2033194 := by exact prefixLift 2033194
  have htrace : WordTrace (prefixWord ++ tailWord_2033194) baseStart_2033194 baseEnd_2033194 := by
    simpa [prefixWord, tailWord_2033194, baseEnd_2033194] using wordTrace_append hprefix tailTrace_2033194
  have hstable : (prefixWord ++ tailWord_2033194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033194).length < 2 ^ (prefixWord ++ tailWord_2033194).sum := by decide
  have hdescent : baseEnd_2033194 < baseStart_2033194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033217 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 8]
def baseStart_2033217 : Nat := 118140960795 + 2033217 * 2 ^ 59
def prefixEnd_2033217 : Nat := 4983230072969 + 3 ^ 40 * 2033217 * 2
def baseEnd_2033217 : Nat := 116001955099186306981879

theorem tailTrace_2033217 : CollatzResearch.WordTrace tailWord_2033217 prefixEnd_2033217 116001955099186306981879 := by
  unfold tailWord_2033217
  simp only [CollatzResearch.WordTrace]
  refine ⟨74157516275009529663057905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49438344183339686442038603 74157516275009529663057905)
  ·
    refine ⟨55618137206257147247293429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74157516275009529663057905 55618137206257147247293429)
    ·
      refine ⟨5214200363086607554433759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55618137206257147247293429 5214200363086607554433759)
      ·
        refine ⟨7821300544629911331650639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214200363086607554433759 7821300544629911331650639)
        ·
          refine ⟨11731950816944866997475959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821300544629911331650639 11731950816944866997475959)
          ·
            refine ⟨17597926225417300496213939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11731950816944866997475959 17597926225417300496213939)
            ·
              refine ⟨26396889338125950744320909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17597926225417300496213939 26396889338125950744320909)
              ·
                refine ⟨9898833501797231529120341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26396889338125950744320909 9898833501797231529120341)
                ·
                  refine ⟨116001955099186306981879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9898833501797231529120341 116001955099186306981879)
                  ·
                    rfl

theorem cell23_2033217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_2033217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033217 prefixEnd_2033217 := by exact prefixLift 2033217
  have htrace : WordTrace (prefixWord ++ tailWord_2033217) baseStart_2033217 baseEnd_2033217 := by
    simpa [prefixWord, tailWord_2033217, baseEnd_2033217] using wordTrace_append hprefix tailTrace_2033217
  have hstable : (prefixWord ++ tailWord_2033217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033217).length < 2 ^ (prefixWord ++ tailWord_2033217).sum := by decide
  have hdescent : baseEnd_2033217 < baseStart_2033217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033234 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_2033234 : Nat := 118140960795 + 2033234 * 2 ^ 59
def prefixEnd_2033234 : Nat := 4983230072969 + 3 ^ 40 * 2033234 * 2
def baseEnd_2033234 : Nat := 116002925007089244036037

theorem tailTrace_2033234 : CollatzResearch.WordTrace tailWord_2033234 prefixEnd_2033234 116002925007089244036037 := by
  unfold tailWord_2033234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539534078986985391606689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49438757543965294377617837 18539534078986985391606689)
  ·
    refine ⟨13904650559240239043705017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18539534078986985391606689 13904650559240239043705017)
    ·
      refine ⟨10428487919430179282778763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13904650559240239043705017 10428487919430179282778763)
      ·
        refine ⟨15642731879145268924168145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10428487919430179282778763 15642731879145268924168145)
        ·
          refine ⟨11732048909358951693126109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15642731879145268924168145 11732048909358951693126109)
          ·
            refine ⟨4399518341009606884922291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11732048909358951693126109 4399518341009606884922291)
            ·
              refine ⟨6599277511514410327383437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399518341009606884922291 6599277511514410327383437)
              ·
                refine ⟨2474729066817903872768789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6599277511514410327383437 2474729066817903872768789)
                ·
                  refine ⟨116002925007089244036037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2474729066817903872768789 116002925007089244036037)
                  ·
                    rfl

theorem cell23_2033234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_2033234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033234 prefixEnd_2033234 := by exact prefixLift 2033234
  have htrace : WordTrace (prefixWord ++ tailWord_2033234) baseStart_2033234 baseEnd_2033234 := by
    simpa [prefixWord, tailWord_2033234, baseEnd_2033234] using wordTrace_append hprefix tailTrace_2033234
  have hstable : (prefixWord ++ tailWord_2033234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033234).length < 2 ^ (prefixWord ++ tailWord_2033234).sum := by decide
  have hdescent : baseEnd_2033234 < baseStart_2033234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033294 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2033294 : Nat := 118140960795 + 2033294 * 2 ^ 59
def prefixEnd_2033294 : Nat := 4983230072969 + 3 ^ 40 * 2033294 * 2
def baseEnd_2033294 : Nat := 348019044634357653858019

theorem tailTrace_2033294 : CollatzResearch.WordTrace tailWord_2033294 prefixEnd_2033294 348019044634357653858019 := by
  unfold tailWord_2033294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270040586966321476701367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49440216463820381209073957 9270040586966321476701367)
  ·
    refine ⟨13905060880449482215052051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270040586966321476701367 13905060880449482215052051)
    ·
      refine ⟨20857591320674223322578077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13905060880449482215052051 20857591320674223322578077)
      ·
        refine ⟨7821596745252833745966779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20857591320674223322578077 7821596745252833745966779)
        ·
          refine ⟨11732395117879250618950169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821596745252833745966779 11732395117879250618950169)
          ·
            refine ⟨8799296338409437964212627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11732395117879250618950169 8799296338409437964212627)
            ·
              refine ⟨13198944507614156946318941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799296338409437964212627 13198944507614156946318941)
              ·
                refine ⟨4949604190355308854869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13198944507614156946318941 4949604190355308854869603)
                ·
                  refine ⟨7424406285532963282304405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949604190355308854869603 7424406285532963282304405)
                  ·
                    refine ⟨348019044634357653858019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7424406285532963282304405 348019044634357653858019)
                    ·
                      rfl

theorem cell23_2033294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2033294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033294 prefixEnd_2033294 := by exact prefixLift 2033294
  have htrace : WordTrace (prefixWord ++ tailWord_2033294) baseStart_2033294 baseEnd_2033294 := by
    simpa [prefixWord, tailWord_2033294, baseEnd_2033294] using wordTrace_append hprefix tailTrace_2033294
  have hstable : (prefixWord ++ tailWord_2033294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033294).length < 2 ^ (prefixWord ++ tailWord_2033294).sum := by decide
  have hdescent : baseEnd_2033294 < baseStart_2033294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033335 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 1, 2, 2]
def baseStart_2033335 : Nat := 118140960795 + 2033335 * 2 ^ 59
def prefixEnd_2033335 : Nat := 4983230072969 + 3 ^ 40 * 2033335 * 2
def baseEnd_2033335 : Nat := 1044078186609907301161369

theorem tailTrace_2033335 : CollatzResearch.WordTrace tailWord_2033335 prefixEnd_2033335 1044078186609907301161369 := by
  unfold tailWord_2033335
  simp only [CollatzResearch.WordTrace]
  refine ⟨74161820088582035815853459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49441213392388023877235639 74161820088582035815853459)
  ·
    refine ⟨111242730132873053723780189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74161820088582035815853459 111242730132873053723780189)
    ·
      refine ⟨41716023799827395146417571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111242730132873053723780189 41716023799827395146417571)
      ·
        refine ⟨62574035699741092719626357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41716023799827395146417571 62574035699741092719626357)
        ·
          refine ⟨5866315846850727442464971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62574035699741092719626357 5866315846850727442464971)
          ·
            refine ⟨8799473770276091163697457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866315846850727442464971 8799473770276091163697457)
            ·
              refine ⟨6599605327707068372773093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8799473770276091163697457 6599605327707068372773093)
              ·
                refine ⟨1237425998945075319894955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6599605327707068372773093 1237425998945075319894955)
                ·
                  refine ⟨1856138998417612979842433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237425998945075319894955 1856138998417612979842433)
                  ·
                    refine ⟨1392104248813209734881825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856138998417612979842433 1392104248813209734881825)
                    ·
                      refine ⟨1044078186609907301161369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392104248813209734881825 1044078186609907301161369)
                      ·
                        rfl

theorem cell23_2033335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_2033335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033335 prefixEnd_2033335 := by exact prefixLift 2033335
  have htrace : WordTrace (prefixWord ++ tailWord_2033335) baseStart_2033335 baseEnd_2033335 := by
    simpa [prefixWord, tailWord_2033335, baseEnd_2033335] using wordTrace_append hprefix tailTrace_2033335
  have hstable : (prefixWord ++ tailWord_2033335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033335).length < 2 ^ (prefixWord ++ tailWord_2033335).sum := by decide
  have hdescent : baseEnd_2033335 < baseStart_2033335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033337 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_2033337 : Nat := 118140960795 + 2033337 * 2 ^ 59
def prefixEnd_2033337 : Nat := 4983230072969 + 3 ^ 40 * 2033337 * 2
def baseEnd_2033337 : Nat := 348026404523738764445453

theorem tailTrace_2033337 : CollatzResearch.WordTrace tailWord_2033337 prefixEnd_2033337 348026404523738764445453 := by
  unfold tailWord_2033337
  simp only [CollatzResearch.WordTrace]
  refine ⟨74161893034574790157426265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49441262023049860104950843 74161893034574790157426265)
  ·
    refine ⟨55621419775931092618069699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74161893034574790157426265 55621419775931092618069699)
    ·
      refine ⟨83432129663896638927104549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55621419775931092618069699 83432129663896638927104549)
      ·
        refine ⟨15643524311980619798832103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83432129663896638927104549 15643524311980619798832103)
        ·
          refine ⟨23465286467970929698248155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15643524311980619798832103 23465286467970929698248155)
          ·
            refine ⟨35197929701956394547372233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23465286467970929698248155 35197929701956394547372233)
            ·
              refine ⟨26398447276467295910529175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35197929701956394547372233 26398447276467295910529175)
              ·
                refine ⟨39597670914700943865793763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26398447276467295910529175 39597670914700943865793763)
                ·
                  refine ⟨59396506372051415798690645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39597670914700943865793763 59396506372051415798690645)
                  ·
                    refine ⟨348026404523738764445453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59396506372051415798690645 348026404523738764445453)
                    ·
                      rfl

theorem cell23_2033337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_2033337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033337 prefixEnd_2033337 := by exact prefixLift 2033337
  have htrace : WordTrace (prefixWord ++ tailWord_2033337) baseStart_2033337 baseEnd_2033337 := by
    simpa [prefixWord, tailWord_2033337, baseEnd_2033337] using wordTrace_append hprefix tailTrace_2033337
  have hstable : (prefixWord ++ tailWord_2033337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033337).length < 2 ^ (prefixWord ++ tailWord_2033337).sum := by decide
  have hdescent : baseEnd_2033337 < baseStart_2033337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033347 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_2033347 : Nat := 118140960795 + 2033347 * 2 ^ 59
def prefixEnd_2033347 : Nat := 4983230072969 + 3 ^ 40 * 2033347 * 2
def baseEnd_2033347 : Nat := 1044084348377761254211313

theorem tailTrace_2033347 : CollatzResearch.WordTrace tailWord_2033347 prefixEnd_2033347 1044084348377761254211313 := by
  unfold tailWord_2033347
  simp only [CollatzResearch.WordTrace]
  refine ⟨74162257764538561865290295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49441505176359041243526863 74162257764538561865290295)
  ·
    refine ⟨111243386646807842797935443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74162257764538561865290295 111243386646807842797935443)
    ·
      refine ⟨166865079970211764196903165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111243386646807842797935443 166865079970211764196903165)
      ·
        refine ⟨62574404988829411573838687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166865079970211764196903165 62574404988829411573838687)
        ·
          refine ⟨93861607483244117360758031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62574404988829411573838687 93861607483244117360758031)
          ·
            refine ⟨140792411224866176041137047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93861607483244117360758031 140792411224866176041137047)
            ·
              refine ⟨211188616837299264061705571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140792411224866176041137047 211188616837299264061705571)
              ·
                refine ⟨316782925255948896092558357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211188616837299264061705571 316782925255948896092558357)
                ·
                  refine ⟨14849199621372604504338673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 316782925255948896092558357 14849199621372604504338673)
                  ·
                    refine ⟨11136899716029453378254005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14849199621372604504338673 11136899716029453378254005)
                    ·
                      refine ⟨1044084348377761254211313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11136899716029453378254005 1044084348377761254211313)
                      ·
                        rfl

theorem cell23_2033347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_2033347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033347 prefixEnd_2033347 := by exact prefixLift 2033347
  have htrace : WordTrace (prefixWord ++ tailWord_2033347) baseStart_2033347 baseEnd_2033347 := by
    simpa [prefixWord, tailWord_2033347, baseEnd_2033347] using wordTrace_append hprefix tailTrace_2033347
  have hstable : (prefixWord ++ tailWord_2033347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033347).length < 2 ^ (prefixWord ++ tailWord_2033347).sum := by decide
  have hdescent : baseEnd_2033347 < baseStart_2033347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033394 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2033394 : Nat := 118140960795 + 2033394 * 2 ^ 59
def prefixEnd_2033394 : Nat := 4983230072969 + 3 ^ 40 * 2033394 * 2
def baseEnd_2033394 : Nat := 1044108481968522570323597

theorem tailTrace_2033394 : CollatzResearch.WordTrace tailWord_2033394 prefixEnd_2033394 1044108481968522570323597 := by
  unfold tailWord_2033394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540992998842072223062809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49442647996912192594834157 18540992998842072223062809)
  ·
    refine ⟨13905744749131554167297107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18540992998842072223062809 13905744749131554167297107)
    ·
      refine ⟨20858617123697331250945661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13905744749131554167297107 20858617123697331250945661)
      ·
        refine ⟨7821981421386499219104623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20858617123697331250945661 7821981421386499219104623)
        ·
          refine ⟨11732972132079748828656935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821981421386499219104623 11732972132079748828656935)
          ·
            refine ⟨17599458198119623242985403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732972132079748828656935 17599458198119623242985403)
            ·
              refine ⟨26399187297179434864478105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17599458198119623242985403 26399187297179434864478105)
              ·
                refine ⟨19799390472884576148358579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26399187297179434864478105 19799390472884576148358579)
                ·
                  refine ⟨29699085709326864222537869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19799390472884576148358579 29699085709326864222537869)
                  ·
                    refine ⟨11137157140997574083451701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29699085709326864222537869 11137157140997574083451701)
                    ·
                      refine ⟨1044108481968522570323597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11137157140997574083451701 1044108481968522570323597)
                      ·
                        rfl

theorem cell23_2033394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2033394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033394 prefixEnd_2033394 := by exact prefixLift 2033394
  have htrace : WordTrace (prefixWord ++ tailWord_2033394) baseStart_2033394 baseEnd_2033394 := by
    simpa [prefixWord, tailWord_2033394, baseEnd_2033394] using wordTrace_append hprefix tailTrace_2033394
  have hstable : (prefixWord ++ tailWord_2033394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033394).length < 2 ^ (prefixWord ++ tailWord_2033394).sum := by decide
  have hdescent : baseEnd_2033394 < baseStart_2033394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033404 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_2033404 : Nat := 118140960795 + 2033404 * 2 ^ 59
def prefixEnd_2033404 : Nat := 4983230072969 + 3 ^ 40 * 2033404 * 2
def baseEnd_2033404 : Nat := 1044113616775067531198551

theorem tailTrace_2033404 : CollatzResearch.WordTrace tailWord_2033404 prefixEnd_2033404 1044113616775067531198551 := by
  unfold tailWord_2033404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082168362666030300057633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49442891150221373733410177 37082168362666030300057633)
  ·
    refine ⟨27811626271999522725043225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37082168362666030300057633 27811626271999522725043225)
    ·
      refine ⟨20858719703999642043782419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27811626271999522725043225 20858719703999642043782419)
      ·
        refine ⟨31288079555999463065673629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20858719703999642043782419 31288079555999463065673629)
        ·
          refine ⟨11733029833499798649627611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31288079555999463065673629 11733029833499798649627611)
          ·
            refine ⟨17599544750249697974441417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11733029833499798649627611 17599544750249697974441417)
            ·
              refine ⟨13199658562687273480831063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17599544750249697974441417 13199658562687273480831063)
              ·
                refine ⟨19799487844030910221246595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13199658562687273480831063 19799487844030910221246595)
                ·
                  refine ⟨29699231766046365331869893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19799487844030910221246595 29699231766046365331869893)
                  ·
                    refine ⟨5568605956133693499725605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29699231766046365331869893 5568605956133693499725605)
                    ·
                      refine ⟨1044113616775067531198551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5568605956133693499725605 1044113616775067531198551)
                      ·
                        rfl

theorem cell23_2033404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_2033404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033404 prefixEnd_2033404 := by exact prefixLift 2033404
  have htrace : WordTrace (prefixWord ++ tailWord_2033404) baseStart_2033404 baseEnd_2033404 := by
    simpa [prefixWord, tailWord_2033404, baseEnd_2033404] using wordTrace_append hprefix tailTrace_2033404
  have hstable : (prefixWord ++ tailWord_2033404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033404).length < 2 ^ (prefixWord ++ tailWord_2033404).sum := by decide
  have hdescent : baseEnd_2033404 < baseStart_2033404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033408 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2]
def baseStart_2033408 : Nat := 118140960795 + 2033408 * 2 ^ 59
def prefixEnd_2033408 : Nat := 4983230072969 + 3 ^ 40 * 2033408 * 2
def baseEnd_2033408 : Nat := 1044115670697685515548533

theorem tailTrace_2033408 : CollatzResearch.WordTrace tailWord_2033408 prefixEnd_2033408 1044115670697685515548533 := by
  unfold tailWord_2033408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082241308658784641630439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49442988411545046188840585 37082241308658784641630439)
  ·
    refine ⟨55623361962988176962445659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37082241308658784641630439 55623361962988176962445659)
    ·
      refine ⟨83435042944482265443668489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55623361962988176962445659 83435042944482265443668489)
      ·
        refine ⟨62576282208361699082751367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83435042944482265443668489 62576282208361699082751367)
        ·
          refine ⟨93864423312542548624127051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62576282208361699082751367 93864423312542548624127051)
          ·
            refine ⟨140796634968813822936190577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93864423312542548624127051 140796634968813822936190577)
            ·
              refine ⟨105597476226610367202142933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140796634968813822936190577 105597476226610367202142933)
              ·
                refine ⟨2474940849061180481300225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105597476226610367202142933 2474940849061180481300225)
                ·
                  refine ⟨1856205636795885360975169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474940849061180481300225 1856205636795885360975169)
                  ·
                    refine ⟨1392154227596914020731377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856205636795885360975169 1392154227596914020731377)
                    ·
                      refine ⟨1044115670697685515548533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392154227596914020731377 1044115670697685515548533)
                      ·
                        rfl

theorem cell23_2033408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_2033408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033408 prefixEnd_2033408 := by exact prefixLift 2033408
  have htrace : WordTrace (prefixWord ++ tailWord_2033408) baseStart_2033408 baseEnd_2033408 := by
    simpa [prefixWord, tailWord_2033408, baseEnd_2033408] using wordTrace_append hprefix tailTrace_2033408
  have hstable : (prefixWord ++ tailWord_2033408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033408).length < 2 ^ (prefixWord ++ tailWord_2033408).sum := by decide
  have hdescent : baseEnd_2033408 < baseStart_2033408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033448 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 5]
def baseStart_2033448 : Nat := 118140960795 + 2033448 * 2 ^ 59
def prefixEnd_2033448 : Nat := 4983230072969 + 3 ^ 40 * 2033448 * 2
def baseEnd_2033448 : Nat := 116015134435985039894261

theorem tailTrace_2033448 : CollatzResearch.WordTrace tailWord_2033448 prefixEnd_2033448 116015134435985039894261 := by
  unfold tailWord_2033448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082970768586328057358499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49443961024781770743144665 37082970768586328057358499)
  ·
    refine ⟨55624456152879492086037749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37082970768586328057358499 55624456152879492086037749)
    ·
      refine ⟨5214792764332452383066039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55624456152879492086037749 5214792764332452383066039)
      ·
        refine ⟨7822189146498678574599059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214792764332452383066039 7822189146498678574599059)
        ·
          refine ⟨11733283719748017861898589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822189146498678574599059 11733283719748017861898589)
          ·
            refine ⟨4399981394905506698211971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11733283719748017861898589 4399981394905506698211971)
            ·
              refine ⟨6599972092358260047317957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399981394905506698211971 6599972092358260047317957)
              ·
                refine ⟨1237494767317173758872117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6599972092358260047317957 1237494767317173758872117)
                ·
                  refine ⟨116015134435985039894261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1237494767317173758872117 116015134435985039894261)
                  ·
                    rfl

theorem cell23_2033448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 5].length) (baseStart_2033448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033448 prefixEnd_2033448 := by exact prefixLift 2033448
  have htrace : WordTrace (prefixWord ++ tailWord_2033448) baseStart_2033448 baseEnd_2033448 := by
    simpa [prefixWord, tailWord_2033448, baseEnd_2033448] using wordTrace_append hprefix tailTrace_2033448
  have hstable : (prefixWord ++ tailWord_2033448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033448).length < 2 ^ (prefixWord ++ tailWord_2033448).sum := by decide
  have hdescent : baseEnd_2033448 < baseStart_2033448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033481 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 6, 2]
def baseStart_2033481 : Nat := 118140960795 + 2033481 * 2 ^ 59
def prefixEnd_2033481 : Nat := 4983230072969 + 3 ^ 40 * 2033481 * 2
def baseEnd_2033481 : Nat := 1044153154785463729935697

theorem tailTrace_2033481 : CollatzResearch.WordTrace tailWord_2033481 prefixEnd_2033481 1044153154785463729935697 := by
  unfold tailWord_2033481
  simp only [CollatzResearch.WordTrace]
  refine ⟨74167145146053102750668297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49444763430702068500445531 74167145146053102750668297)
  ·
    refine ⟨55625358859539827063001223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74167145146053102750668297 55625358859539827063001223)
    ·
      refine ⟨83438038289309740594501835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55625358859539827063001223 83438038289309740594501835)
      ·
        refine ⟨125157057433964610891752753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83438038289309740594501835 125157057433964610891752753)
        ·
          refine ⟨93867793075473458168814565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125157057433964610891752753 93867793075473458168814565)
          ·
            refine ⟨17600211201651273406652731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93867793075473458168814565 17600211201651273406652731)
            ·
              refine ⟨26400316802476910109979097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17600211201651273406652731 26400316802476910109979097)
              ·
                refine ⟨19800237601857682582484323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26400316802476910109979097 19800237601857682582484323)
                ·
                  refine ⟨29700356402786523873726485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19800237601857682582484323 29700356402786523873726485)
                  ·
                    refine ⟨1392204206380618306580929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29700356402786523873726485 1392204206380618306580929)
                    ·
                      refine ⟨1044153154785463729935697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392204206380618306580929 1044153154785463729935697)
                      ·
                        rfl

theorem cell23_2033481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6, 2].length) (baseStart_2033481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033481 prefixEnd_2033481 := by exact prefixLift 2033481
  have htrace : WordTrace (prefixWord ++ tailWord_2033481) baseStart_2033481 baseEnd_2033481 := by
    simpa [prefixWord, tailWord_2033481, baseEnd_2033481] using wordTrace_append hprefix tailTrace_2033481
  have hstable : (prefixWord ++ tailWord_2033481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033481).length < 2 ^ (prefixWord ++ tailWord_2033481).sum := by decide
  have hdescent : baseEnd_2033481 < baseStart_2033481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033518 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2033518 : Nat := 118140960795 + 2033518 * 2 ^ 59
def prefixEnd_2033518 : Nat := 4983230072969 + 3 ^ 40 * 2033518 * 2
def baseEnd_2033518 : Nat := 1044172153569680085173027

theorem tailTrace_2033518 : CollatzResearch.WordTrace tailWord_2033518 prefixEnd_2033518 1044172153569680085173027 := by
  unfold tailWord_2033518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271061830864882258720651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49445663097946038713176805 9271061830864882258720651)
  ·
    refine ⟨13906592746297323388080977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9271061830864882258720651 13906592746297323388080977)
    ·
      refine ⟨10429944559722992541060733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13906592746297323388080977 10429944559722992541060733)
      ·
        refine ⟨3911229209896122202897775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10429944559722992541060733 3911229209896122202897775)
        ·
          refine ⟨5866843814844183304346663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911229209896122202897775 5866843814844183304346663)
          ·
            refine ⟨8800265722266274956519995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866843814844183304346663 8800265722266274956519995)
            ·
              refine ⟨13200398583399412434779993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800265722266274956519995 13200398583399412434779993)
              ·
                refine ⟨9900298937549559326084995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200398583399412434779993 9900298937549559326084995)
                ·
                  refine ⟨14850448406324338989127493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900298937549559326084995 14850448406324338989127493)
                  ·
                    refine ⟨2784459076185813560461405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14850448406324338989127493 2784459076185813560461405)
                    ·
                      refine ⟨1044172153569680085173027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2784459076185813560461405 1044172153569680085173027)
                      ·
                        rfl

theorem cell23_2033518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2033518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033518 prefixEnd_2033518 := by exact prefixLift 2033518
  have htrace : WordTrace (prefixWord ++ tailWord_2033518) baseStart_2033518 baseEnd_2033518 := by
    simpa [prefixWord, tailWord_2033518, baseEnd_2033518] using wordTrace_append hprefix tailTrace_2033518
  have hstable : (prefixWord ++ tailWord_2033518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033518).length < 2 ^ (prefixWord ++ tailWord_2033518).sum := by decide
  have hdescent : baseEnd_2033518 < baseStart_2033518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033565 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2033565 : Nat := 118140960795 + 2033565 * 2 ^ 59
def prefixEnd_2033565 : Nat := 4983230072969 + 3 ^ 40 * 2033565 * 2
def baseEnd_2033565 : Nat := 1044196287160441401285311

theorem tailTrace_2033565 : CollatzResearch.WordTrace tailWord_2033565 prefixEnd_2033565 1044196287160441401285311 := by
  unfold tailWord_2033565
  simp only [CollatzResearch.WordTrace]
  refine ⟨74170208877748785096726149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49446805918499190064484099 74170208877748785096726149)
  ·
    refine ⟨13906914164577897205636153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74170208877748785096726149 13906914164577897205636153)
    ·
      refine ⟨10430185623433422904227115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13906914164577897205636153 10430185623433422904227115)
      ·
        refine ⟨15645278435150134356340673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430185623433422904227115 15645278435150134356340673)
        ·
          refine ⟨11733958826362600767255505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15645278435150134356340673 11733958826362600767255505)
          ·
            refine ⟨8800469119771950575441629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11733958826362600767255505 8800469119771950575441629)
            ·
              refine ⟨3300175919914481465790611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8800469119771950575441629 3300175919914481465790611)
              ·
                refine ⟨4950263879871722198685917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300175919914481465790611 4950263879871722198685917)
                ·
                  refine ⟨1856348954951895824507219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4950263879871722198685917 1856348954951895824507219)
                  ·
                    refine ⟨2784523432427843736760829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1856348954951895824507219 2784523432427843736760829)
                    ·
                      refine ⟨1044196287160441401285311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2784523432427843736760829 1044196287160441401285311)
                      ·
                        rfl

theorem cell23_2033565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2033565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033565 prefixEnd_2033565 := by exact prefixLift 2033565
  have htrace : WordTrace (prefixWord ++ tailWord_2033565) baseStart_2033565 baseEnd_2033565 := by
    simpa [prefixWord, tailWord_2033565, baseEnd_2033565] using wordTrace_append hprefix tailTrace_2033565
  have hstable : (prefixWord ++ tailWord_2033565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033565).length < 2 ^ (prefixWord ++ tailWord_2033565).sum := by decide
  have hdescent : baseEnd_2033565 < baseStart_2033565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033571 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2033571 : Nat := 118140960795 + 2033571 * 2 ^ 59
def prefixEnd_2033571 : Nat := 4983230072969 + 3 ^ 40 * 2033571 * 2
def baseEnd_2033571 : Nat := 1044199368044368377810283

theorem tailTrace_2033571 : CollatzResearch.WordTrace tailWord_2033571 prefixEnd_2033571 1044199368044368377810283 := by
  unfold tailWord_2033571
  simp only [CollatzResearch.WordTrace]
  refine ⟨74170427715727048121444567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49446951810484698747629711 74170427715727048121444567)
  ·
    refine ⟨111255641573590572182166851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74170427715727048121444567 111255641573590572182166851)
    ·
      refine ⟨166883462360385858273250277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111255641573590572182166851 166883462360385858273250277)
      ·
        refine ⟨31290649192572348426234427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166883462360385858273250277 31290649192572348426234427)
        ·
          refine ⟨46935973788858522639351641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31290649192572348426234427 46935973788858522639351641)
          ·
            refine ⟨35201980341643891979513731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46935973788858522639351641 35201980341643891979513731)
            ·
              refine ⟨52802970512465837969270597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35201980341643891979513731 52802970512465837969270597)
              ·
                refine ⟨9900556971087344619238237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52802970512465837969270597 9900556971087344619238237)
                ·
                  refine ⟨3712708864157754232214339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9900556971087344619238237 3712708864157754232214339)
                  ·
                    refine ⟨5569063296236631348321509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712708864157754232214339 5569063296236631348321509)
                    ·
                      refine ⟨1044199368044368377810283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5569063296236631348321509 1044199368044368377810283)
                      ·
                        rfl

theorem cell23_2033571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2033571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033571 prefixEnd_2033571 := by exact prefixLift 2033571
  have htrace : WordTrace (prefixWord ++ tailWord_2033571) baseStart_2033571 baseEnd_2033571 := by
    simpa [prefixWord, tailWord_2033571, baseEnd_2033571] using wordTrace_append hprefix tailTrace_2033571
  have hstable : (prefixWord ++ tailWord_2033571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033571).length < 2 ^ (prefixWord ++ tailWord_2033571).sum := by decide
  have hdescent : baseEnd_2033571 < baseStart_2033571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033585 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_2033585 : Nat := 118140960795 + 2033585 * 2 ^ 59
def prefixEnd_2033585 : Nat := 4983230072969 + 3 ^ 40 * 2033585 * 2
def baseEnd_2033585 : Nat := 348068852257843774345073

theorem tailTrace_2033585 : CollatzResearch.WordTrace tailWord_2033585 prefixEnd_2033585 348068852257843774345073 := by
  unfold tailWord_2033585
  simp only [CollatzResearch.WordTrace]
  refine ⟨74170938337676328512454209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49447292225117552341636139 74170938337676328512454209)
  ·
    refine ⟨55628203753257246384340657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74170938337676328512454209 55628203753257246384340657)
    ·
      refine ⟨41721152814942934788255493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55628203753257246384340657 41721152814942934788255493)
      ·
        refine ⟨7822716152801800272797905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41721152814942934788255493 7822716152801800272797905)
        ·
          refine ⟨5867037114601350204598429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7822716152801800272797905 5867037114601350204598429)
          ·
            refine ⟨2200138917975506326724411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5867037114601350204598429 2200138917975506326724411)
            ·
              refine ⟨3300208376963259490086617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200138917975506326724411 3300208376963259490086617)
              ·
                refine ⟨2475156282722444617564963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300208376963259490086617 2475156282722444617564963)
                ·
                  refine ⟨3712734424083666926347445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475156282722444617564963 3712734424083666926347445)
                  ·
                    refine ⟨348068852257843774345073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3712734424083666926347445 348068852257843774345073)
                    ·
                      rfl

theorem cell23_2033585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_2033585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033585 prefixEnd_2033585 := by exact prefixLift 2033585
  have htrace : WordTrace (prefixWord ++ tailWord_2033585) baseStart_2033585 baseEnd_2033585 := by
    simpa [prefixWord, tailWord_2033585, baseEnd_2033585] using wordTrace_append hprefix tailTrace_2033585
  have hstable : (prefixWord ++ tailWord_2033585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033585).length < 2 ^ (prefixWord ++ tailWord_2033585).sum := by decide
  have hdescent : baseEnd_2033585 < baseStart_2033585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033598 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2033598 : Nat := 118140960795 + 2033598 * 2 ^ 59
def prefixEnd_2033598 : Nat := 4983230072969 + 3 ^ 40 * 2033598 * 2
def baseEnd_2033598 : Nat := 348071077340679924057553

theorem tailTrace_2033598 : CollatzResearch.WordTrace tailWord_2033598 prefixEnd_2033598 348071077340679924057553 := by
  unfold tailWord_2033598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271426560828653966584681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49447608324419487821784965 9271426560828653966584681)
  ·
    refine ⟨6953569920621490474938511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9271426560828653966584681 6953569920621490474938511)
    ·
      refine ⟨10430354880932235712407767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953569920621490474938511 10430354880932235712407767)
      ·
        refine ⟨15645532321398353568611651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430354880932235712407767 15645532321398353568611651)
        ·
          refine ⟨23468298482097530352917477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15645532321398353568611651 23468298482097530352917477)
          ·
            refine ⟨4400305965393286941172027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23468298482097530352917477 4400305965393286941172027)
            ·
              refine ⟨6600458948089930411758041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400305965393286941172027 6600458948089930411758041)
              ·
                refine ⟨4950344211067447808818531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6600458948089930411758041 4950344211067447808818531)
                ·
                  refine ⟨7425516316601171713227797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950344211067447808818531 7425516316601171713227797)
                  ·
                    refine ⟨348071077340679924057553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7425516316601171713227797 348071077340679924057553)
                    ·
                      rfl

theorem cell23_2033598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2033598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033598 prefixEnd_2033598 := by exact prefixLift 2033598
  have htrace : WordTrace (prefixWord ++ tailWord_2033598) baseStart_2033598 baseEnd_2033598 := by
    simpa [prefixWord, tailWord_2033598, baseEnd_2033598] using wordTrace_append hprefix tailTrace_2033598
  have hstable : (prefixWord ++ tailWord_2033598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033598).length < 2 ^ (prefixWord ++ tailWord_2033598).sum := by decide
  have hdescent : baseEnd_2033598 < baseStart_2033598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033608 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_2033608 : Nat := 118140960795 + 2033608 * 2 ^ 59
def prefixEnd_2033608 : Nat := 4983230072969 + 3 ^ 40 * 2033608 * 2
def baseEnd_2033608 : Nat := 1044218366828584733047613

theorem tailTrace_2033608 : CollatzResearch.WordTrace tailWord_2033608 prefixEnd_2033608 1044218366828584733047613 := by
  unfold tailWord_2033608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085888608296501720270739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49447851477728668960360985 37085888608296501720270739)
  ·
    refine ⟨55628832912444752580406109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37085888608296501720270739 55628832912444752580406109)
    ·
      refine ⟨20860812342166782217652291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55628832912444752580406109 20860812342166782217652291)
      ·
        refine ⟨31291218513250173326478437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20860812342166782217652291 31291218513250173326478437)
        ·
          refine ⟨5867103471234407498714707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31291218513250173326478437 5867103471234407498714707)
          ·
            refine ⟨8800655206851611248072061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867103471234407498714707 8800655206851611248072061)
            ·
              refine ⟨3300245702569354218027023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8800655206851611248072061 3300245702569354218027023)
              ·
                refine ⟨4950368553854031327040535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300245702569354218027023 4950368553854031327040535)
                ·
                  refine ⟨7425552830781046990560803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950368553854031327040535 7425552830781046990560803)
                  ·
                    refine ⟨11138329246171570485841205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425552830781046990560803 11138329246171570485841205)
                    ·
                      refine ⟨1044218366828584733047613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11138329246171570485841205 1044218366828584733047613)
                      ·
                        rfl

theorem cell23_2033608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_2033608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033608 prefixEnd_2033608 := by exact prefixLift 2033608
  have htrace : WordTrace (prefixWord ++ tailWord_2033608) baseStart_2033608 baseEnd_2033608 := by
    simpa [prefixWord, tailWord_2033608, baseEnd_2033608] using wordTrace_append hprefix tailTrace_2033608
  have hstable : (prefixWord ++ tailWord_2033608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033608).length < 2 ^ (prefixWord ++ tailWord_2033608).sum := by decide
  have hdescent : baseEnd_2033608 < baseStart_2033608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033681 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_2033681 : Nat := 118140960795 + 2033681 * 2 ^ 59
def prefixEnd_2033681 : Nat := 4983230072969 + 3 ^ 40 * 2033681 * 2
def baseEnd_2033681 : Nat := 1044255850916362947434777

theorem tailTrace_2033681 : CollatzResearch.WordTrace tailWord_2033681 prefixEnd_2033681 1044255850916362947434777 := by
  unfold tailWord_2033681
  simp only [CollatzResearch.WordTrace]
  refine ⟨74174439745328536907948897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49449626496885691271965931 74174439745328536907948897)
  ·
    refine ⟨55630829808996402680961673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74174439745328536907948897 55630829808996402680961673)
    ·
      refine ⟨41723122356747302010721255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55630829808996402680961673 41723122356747302010721255)
      ·
        refine ⟨62584683535120953016081883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41723122356747302010721255 62584683535120953016081883)
        ·
          refine ⟨93877025302681429524122825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62584683535120953016081883 93877025302681429524122825)
          ·
            refine ⟨70407768977011072143092119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93877025302681429524122825 70407768977011072143092119)
            ·
              refine ⟨105611653465516608214638179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70407768977011072143092119 105611653465516608214638179)
              ·
                refine ⟨158417480198274912321957269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105611653465516608214638179 158417480198274912321957269)
                ·
                  refine ⟨7425819384294136515091747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158417480198274912321957269 7425819384294136515091747)
                  ·
                    refine ⟨11138729076441204772637621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425819384294136515091747 11138729076441204772637621)
                    ·
                      refine ⟨1044255850916362947434777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11138729076441204772637621 1044255850916362947434777)
                      ·
                        rfl

theorem cell23_2033681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_2033681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033681 prefixEnd_2033681 := by exact prefixLift 2033681
  have htrace : WordTrace (prefixWord ++ tailWord_2033681) baseStart_2033681 baseEnd_2033681 := by
    simpa [prefixWord, tailWord_2033681, baseEnd_2033681] using wordTrace_append hprefix tailTrace_2033681
  have hstable : (prefixWord ++ tailWord_2033681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033681).length < 2 ^ (prefixWord ++ tailWord_2033681).sum := by decide
  have hdescent : baseEnd_2033681 < baseStart_2033681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033691 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_2033691 : Nat := 118140960795 + 2033691 * 2 ^ 59
def prefixEnd_2033691 : Nat := 4983230072969 + 3 ^ 40 * 2033691 * 2
def baseEnd_2033691 : Nat := 1044260985722907908309731

theorem tailTrace_2033691 : CollatzResearch.WordTrace tailWord_2033691 prefixEnd_2033691 1044260985722907908309731 := by
  unfold tailWord_2033691
  simp only [CollatzResearch.WordTrace]
  refine ⟨74174804475292308615812927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49449869650194872410541951 74174804475292308615812927)
  ·
    refine ⟨111262206712938462923719391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74174804475292308615812927 111262206712938462923719391)
    ·
      refine ⟨166893310069407694385579087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111262206712938462923719391 166893310069407694385579087)
      ·
        refine ⟨250339965104111541578368631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166893310069407694385579087 250339965104111541578368631)
        ·
          refine ⟨375509947656167312367552947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250339965104111541578368631 375509947656167312367552947)
          ·
            refine ⟨563264921484250968551329421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375509947656167312367552947 563264921484250968551329421)
            ·
              refine ⟨211224345556594113206748533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563264921484250968551329421 211224345556594113206748533)
              ·
                refine ⟨19802282395930698113132675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211224345556594113206748533 19802282395930698113132675)
                ·
                  refine ⟨29703423593896047169699013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19802282395930698113132675 29703423593896047169699013)
                  ·
                    refine ⟨5569391923855508844318565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29703423593896047169699013 5569391923855508844318565)
                    ·
                      refine ⟨1044260985722907908309731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5569391923855508844318565 1044260985722907908309731)
                      ·
                        rfl

theorem cell23_2033691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_2033691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033691 prefixEnd_2033691 := by exact prefixLift 2033691
  have htrace : WordTrace (prefixWord ++ tailWord_2033691) baseStart_2033691 baseEnd_2033691 := by
    simpa [prefixWord, tailWord_2033691, baseEnd_2033691] using wordTrace_append hprefix tailTrace_2033691
  have hstable : (prefixWord ++ tailWord_2033691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033691).length < 2 ^ (prefixWord ++ tailWord_2033691).sum := by decide
  have hdescent : baseEnd_2033691 < baseStart_2033691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033698 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2033698 : Nat := 118140960795 + 2033698 * 2 ^ 59
def prefixEnd_2033698 : Nat := 4983230072969 + 3 ^ 40 * 2033698 * 2
def baseEnd_2033698 : Nat := 1044264580087489380922199

theorem tailTrace_2033698 : CollatzResearch.WordTrace tailWord_2033698 prefixEnd_2033698 1044264580087489380922199 := by
  unfold tailWord_2033698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543764946566737202829437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49450039857511299207545165 18543764946566737202829437)
  ·
    refine ⟨6953911854962526451061039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18543764946566737202829437 6953911854962526451061039)
    ·
      refine ⟨10430867782443789676591559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953911854962526451061039 10430867782443789676591559)
      ·
        refine ⟨15646301673665684514887339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430867782443789676591559 15646301673665684514887339)
        ·
          refine ⟨23469452510498526772331009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15646301673665684514887339 23469452510498526772331009)
          ·
            refine ⟨17602089382873895079248257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23469452510498526772331009 17602089382873895079248257)
            ·
              refine ⟨13201567037155421309436193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17602089382873895079248257 13201567037155421309436193)
              ·
                refine ⟨9901175277866565982077145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13201567037155421309436193 9901175277866565982077145)
                ·
                  refine ⟨7425881458399924486557859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901175277866565982077145 7425881458399924486557859)
                  ·
                    refine ⟨11138822187599886729836789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7425881458399924486557859 11138822187599886729836789)
                    ·
                      refine ⟨1044264580087489380922199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11138822187599886729836789 1044264580087489380922199)
                      ·
                        rfl

theorem cell23_2033698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2033698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033698 prefixEnd_2033698 := by exact prefixLift 2033698
  have htrace : WordTrace (prefixWord ++ tailWord_2033698) baseStart_2033698 baseEnd_2033698 := by
    simpa [prefixWord, tailWord_2033698, baseEnd_2033698] using wordTrace_append hprefix tailTrace_2033698
  have hstable : (prefixWord ++ tailWord_2033698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033698).length < 2 ^ (prefixWord ++ tailWord_2033698).sum := by decide
  have hdescent : baseEnd_2033698 < baseStart_2033698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033731 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 7]
def baseStart_2033731 : Nat := 118140960795 + 2033731 * 2 ^ 59
def prefixEnd_2033731 : Nat := 4983230072969 + 3 ^ 40 * 2033731 * 2
def baseEnd_2033731 : Nat := 348093841649695917269849

theorem tailTrace_2033731 : CollatzResearch.WordTrace tailWord_2033731 prefixEnd_2033731 348093841649695917269849 := by
  unfold tailWord_2033731
  simp only [CollatzResearch.WordTrace]
  refine ⟨74176263395147395447269047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49450842263431596964846031 74176263395147395447269047)
  ·
    refine ⟨111264395092721093170903571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74176263395147395447269047 111264395092721093170903571)
    ·
      refine ⟨166896592639081639756355357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111264395092721093170903571 166896592639081639756355357)
      ·
        refine ⟨62586222239655614908633259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166896592639081639756355357 62586222239655614908633259)
        ·
          refine ⟨93879333359483422362949889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62586222239655614908633259 93879333359483422362949889)
          ·
            refine ⟨70409500019612566772212417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93879333359483422362949889 70409500019612566772212417)
            ·
              refine ⟨52807125014709425079159313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70409500019612566772212417 52807125014709425079159313)
              ·
                refine ⟨39605343761032068809369485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52807125014709425079159313 39605343761032068809369485)
                ·
                  refine ⟨14852003910387025803513557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39605343761032068809369485 14852003910387025803513557)
                  ·
                    refine ⟨348093841649695917269849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14852003910387025803513557 348093841649695917269849)
                    ·
                      rfl

theorem cell23_2033731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_2033731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033731 prefixEnd_2033731 := by exact prefixLift 2033731
  have htrace : WordTrace (prefixWord ++ tailWord_2033731) baseStart_2033731 baseEnd_2033731 := by
    simpa [prefixWord, tailWord_2033731, baseEnd_2033731] using wordTrace_append hprefix tailTrace_2033731
  have hstable : (prefixWord ++ tailWord_2033731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033731).length < 2 ^ (prefixWord ++ tailWord_2033731).sum := by decide
  have hdescent : baseEnd_2033731 < baseStart_2033731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033748 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_2033748 : Nat := 118140960795 + 2033748 * 2 ^ 59
def prefixEnd_2033748 : Nat := 4983230072969 + 3 ^ 40 * 2033748 * 2
def baseEnd_2033748 : Nat := 348096751373404728432323

theorem tailTrace_2033748 : CollatzResearch.WordTrace tailWord_2033748 prefixEnd_2033748 348096751373404728432323 := by
  unfold tailWord_2033748
  simp only [CollatzResearch.WordTrace]
  refine ⟨37088441718042903675318949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49451255624057204900425265 37088441718042903675318949)
  ·
    refine ⟨6954082822133044439122303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37088441718042903675318949 6954082822133044439122303)
    ·
      refine ⟨10431124233199566658683455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954082822133044439122303 10431124233199566658683455)
      ·
        refine ⟨15646686349799349988025183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431124233199566658683455 15646686349799349988025183)
        ·
          refine ⟨23470029524699024982037775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15646686349799349988025183 23470029524699024982037775)
          ·
            refine ⟨35205044287048537473056663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23470029524699024982037775 35205044287048537473056663)
            ·
              refine ⟨52807566430572806209584995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35205044287048537473056663 52807566430572806209584995)
              ·
                refine ⟨79211349645859209314377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52807566430572806209584995 79211349645859209314377493)
                ·
                  refine ⟨3713032014649650436611445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79211349645859209314377493 3713032014649650436611445)
                  ·
                    refine ⟨348096751373404728432323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3713032014649650436611445 348096751373404728432323)
                    ·
                      rfl

theorem cell23_2033748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_2033748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033748 prefixEnd_2033748 := by exact prefixLift 2033748
  have htrace : WordTrace (prefixWord ++ tailWord_2033748) baseStart_2033748 baseEnd_2033748 := by
    simpa [prefixWord, tailWord_2033748, baseEnd_2033748] using wordTrace_append hprefix tailTrace_2033748
  have hstable : (prefixWord ++ tailWord_2033748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033748).length < 2 ^ (prefixWord ++ tailWord_2033748).sum := by decide
  have hdescent : baseEnd_2033748 < baseStart_2033748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033765 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_2033765 : Nat := 118140960795 + 2033765 * 2 ^ 59
def prefixEnd_2033765 : Nat := 4983230072969 + 3 ^ 40 * 2033765 * 2
def baseEnd_2033765 : Nat := 348099661097113539594797

theorem tailTrace_2033765 : CollatzResearch.WordTrace tailWord_2033765 prefixEnd_2033765 348099661097113539594797 := by
  unfold tailWord_2033765
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177503477024219254006749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49451668984682812836004499 74177503477024219254006749)
  ·
    refine ⟨27816563803884082220252531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74177503477024219254006749 27816563803884082220252531)
    ·
      refine ⟨41724845705826123330378797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27816563803884082220252531 41724845705826123330378797)
      ·
        refine ⟨15646817139684796248892049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41724845705826123330378797 15646817139684796248892049)
        ·
          refine ⟨11735112854763597186669037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15646817139684796248892049 11735112854763597186669037)
          ·
            refine ⟨4400667320536348945000889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11735112854763597186669037 4400667320536348945000889)
            ·
              refine ⟨3300500490402261708750667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400667320536348945000889 3300500490402261708750667)
              ·
                refine ⟨4950750735603392563126001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300500490402261708750667 4950750735603392563126001)
                ·
                  refine ⟨3713063051702544422344501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950750735603392563126001 3713063051702544422344501)
                  ·
                    refine ⟨348099661097113539594797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3713063051702544422344501 348099661097113539594797)
                    ·
                      rfl

theorem cell23_2033765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_2033765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033765 prefixEnd_2033765 := by exact prefixLift 2033765
  have htrace : WordTrace (prefixWord ++ tailWord_2033765) baseStart_2033765 baseEnd_2033765 := by
    simpa [prefixWord, tailWord_2033765, baseEnd_2033765] using wordTrace_append hprefix tailTrace_2033765
  have hstable : (prefixWord ++ tailWord_2033765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033765).length < 2 ^ (prefixWord ++ tailWord_2033765).sum := by decide
  have hdescent : baseEnd_2033765 < baseStart_2033765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033771 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_2033771 : Nat := 118140960795 + 2033771 * 2 ^ 59
def prefixEnd_2033771 : Nat := 4983230072969 + 3 ^ 40 * 2033771 * 2
def baseEnd_2033771 : Nat := 1044302064175267595309363

theorem tailTrace_2033771 : CollatzResearch.WordTrace tailWord_2033771 prefixEnd_2033771 1044302064175267595309363 := by
  unfold tailWord_2033771
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177722315002482278725167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49451814876668321519150111 74177722315002482278725167)
  ·
    refine ⟨111266583472503723418087751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74177722315002482278725167 111266583472503723418087751)
    ·
      refine ⟨166899875208755585127131627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111266583472503723418087751 166899875208755585127131627)
      ·
        refine ⟨250349812813133377690697441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166899875208755585127131627 250349812813133377690697441)
        ·
          refine ⟨187762359609850033268023081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250349812813133377690697441 187762359609850033268023081)
          ·
            refine ⟨140821769707387524951017311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187762359609850033268023081 140821769707387524951017311)
            ·
              refine ⟨211232654561081287426525967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140821769707387524951017311 211232654561081287426525967)
              ·
                refine ⟨316848981841621931139788951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211232654561081287426525967 316848981841621931139788951)
                ·
                  refine ⟨475273472762432896709683427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316848981841621931139788951 475273472762432896709683427)
                  ·
                    refine ⟨712910209143649345064525141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 475273472762432896709683427 712910209143649345064525141)
                    ·
                      refine ⟨1044302064175267595309363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 712910209143649345064525141 1044302064175267595309363)
                      ·
                        rfl

theorem cell23_2033771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_2033771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033771 prefixEnd_2033771 := by exact prefixLift 2033771
  have htrace : WordTrace (prefixWord ++ tailWord_2033771) baseStart_2033771 baseEnd_2033771 := by
    simpa [prefixWord, tailWord_2033771, baseEnd_2033771] using wordTrace_append hprefix tailTrace_2033771
  have hstable : (prefixWord ++ tailWord_2033771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033771).length < 2 ^ (prefixWord ++ tailWord_2033771).sum := by decide
  have hdescent : baseEnd_2033771 < baseStart_2033771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033785 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2033785 : Nat := 118140960795 + 2033785 * 2 ^ 59
def prefixEnd_2033785 : Nat := 4983230072969 + 3 ^ 40 * 2033785 * 2
def baseEnd_2033785 : Nat := 1044309252904430540534299

theorem tailTrace_2033785 : CollatzResearch.WordTrace tailWord_2033785 prefixEnd_2033785 1044309252904430540534299 := by
  unfold tailWord_2033785
  simp only [CollatzResearch.WordTrace]
  refine ⟨74178232936951762669734809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49452155291301175113156539 74178232936951762669734809)
  ·
    refine ⟨55633674702713822002301107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74178232936951762669734809 55633674702713822002301107)
    ·
      refine ⟨83450512054070733003451661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55633674702713822002301107 83450512054070733003451661)
      ·
        refine ⟨31293942020276524876294373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83450512054070733003451661 31293942020276524876294373)
        ·
          refine ⟨5867614128801848414305195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31293942020276524876294373 5867614128801848414305195)
          ·
            refine ⟨8801421193202772621457793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867614128801848414305195 8801421193202772621457793)
            ·
              refine ⟨6601065894902079466093345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8801421193202772621457793 6601065894902079466093345)
              ·
                refine ⟨4950799421176559599570009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601065894902079466093345 4950799421176559599570009)
                ·
                  refine ⟨3713099565882419699677507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950799421176559599570009 3713099565882419699677507)
                  ·
                    refine ⟨5569649348823629549516261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713099565882419699677507 5569649348823629549516261)
                    ·
                      refine ⟨1044309252904430540534299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5569649348823629549516261 1044309252904430540534299)
                      ·
                        rfl

theorem cell23_2033785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2033785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033785 prefixEnd_2033785 := by exact prefixLift 2033785
  have htrace : WordTrace (prefixWord ++ tailWord_2033785) baseStart_2033785 baseEnd_2033785 := by
    simpa [prefixWord, tailWord_2033785, baseEnd_2033785] using wordTrace_append hprefix tailTrace_2033785
  have hstable : (prefixWord ++ tailWord_2033785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033785).length < 2 ^ (prefixWord ++ tailWord_2033785).sum := by decide
  have hdescent : baseEnd_2033785 < baseStart_2033785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033802 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2033802 : Nat := 118140960795 + 2033802 * 2 ^ 59
def prefixEnd_2033802 : Nat := 4983230072969 + 3 ^ 40 * 2033802 * 2
def baseEnd_2033802 : Nat := 1044317982075556974021721

theorem tailTrace_2033802 : CollatzResearch.WordTrace tailWord_2033802 prefixEnd_2033802 1044317982075556974021721 := by
  unfold tailWord_2033802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544713244472543643275915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49452568651926783048735773 18544713244472543643275915)
  ·
    refine ⟨27817069866708815464913873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18544713244472543643275915 27817069866708815464913873)
    ·
      refine ⟨20862802400031611598685405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27817069866708815464913873 20862802400031611598685405)
      ·
        refine ⟨7823550900011854349507027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20862802400031611598685405 7823550900011854349507027)
        ·
          refine ⟨11735326350017781524260541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823550900011854349507027 11735326350017781524260541)
          ·
            refine ⟨4400747381256668071597703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11735326350017781524260541 4400747381256668071597703)
            ·
              refine ⟨6601121071885002107396555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400747381256668071597703 6601121071885002107396555)
              ·
                refine ⟨9901681607827503161094833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601121071885002107396555 9901681607827503161094833)
                ·
                  refine ⟨7426261205870627370821125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901681607827503161094833 7426261205870627370821125)
                  ·
                    refine ⟨1392423976100742632028961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426261205870627370821125 1392423976100742632028961)
                    ·
                      refine ⟨1044317982075556974021721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392423976100742632028961 1044317982075556974021721)
                      ·
                        rfl

theorem cell23_2033802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2033802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033802 prefixEnd_2033802 := by exact prefixLift 2033802
  have htrace : WordTrace (prefixWord ++ tailWord_2033802) baseStart_2033802 baseEnd_2033802 := by
    simpa [prefixWord, tailWord_2033802, baseEnd_2033802] using wordTrace_append hprefix tailTrace_2033802
  have hstable : (prefixWord ++ tailWord_2033802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033802).length < 2 ^ (prefixWord ++ tailWord_2033802).sum := by decide
  have hdescent : baseEnd_2033802 < baseStart_2033802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033808 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 6]
def baseStart_2033808 : Nat := 118140960795 + 2033808 * 2 ^ 59
def prefixEnd_2033808 : Nat := 4983230072969 + 3 ^ 40 * 2033808 * 2
def baseEnd_2033808 : Nat := 116035673662164883394077

theorem tailTrace_2033808 : CollatzResearch.WordTrace tailWord_2033808 prefixEnd_2033808 116035673662164883394077 := by
  unfold tailWord_2033808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089535907934218798911039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49452714543912291731881385 37089535907934218798911039)
  ·
    refine ⟨55634303861901328198366559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089535907934218798911039 55634303861901328198366559)
    ·
      refine ⟨83451455792851992297549839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55634303861901328198366559 83451455792851992297549839)
      ·
        refine ⟨125177183689277988446324759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83451455792851992297549839 125177183689277988446324759)
        ·
          refine ⟨187765775533916982669487139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125177183689277988446324759 187765775533916982669487139)
          ·
            refine ⟨281648663300875474004230709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187765775533916982669487139 281648663300875474004230709)
            ·
              refine ⟨26404562184457075687896629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281648663300875474004230709 26404562184457075687896629)
              ·
                refine ⟨2475427704792850845740309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26404562184457075687896629 2475427704792850845740309)
                ·
                  refine ⟨116035673662164883394077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2475427704792850845740309 116035673662164883394077)
                  ·
                    rfl

theorem cell23_2033808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_2033808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033808 prefixEnd_2033808 := by exact prefixLift 2033808
  have htrace : WordTrace (prefixWord ++ tailWord_2033808) baseStart_2033808 baseEnd_2033808 := by
    simpa [prefixWord, tailWord_2033808, baseEnd_2033808] using wordTrace_append hprefix tailTrace_2033808
  have hstable : (prefixWord ++ tailWord_2033808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033808).length < 2 ^ (prefixWord ++ tailWord_2033808).sum := by decide
  have hdescent : baseEnd_2033808 < baseStart_2033808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033902 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2033902 : Nat := 118140960795 + 2033902 * 2 ^ 59
def prefixEnd_2033902 : Nat := 4983230072969 + 3 ^ 40 * 2033902 * 2
def baseEnd_2033902 : Nat := 348123110047002194257087

theorem tailTrace_2033902 : CollatzResearch.WordTrace tailWord_2033902 prefixEnd_2033902 348123110047002194257087 := by
  unfold tailWord_2033902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272812534690986456467995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49455000185018594434495973 9272812534690986456467995)
  ·
    refine ⟨13909218802036479684701993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272812534690986456467995 13909218802036479684701993)
    ·
      refine ⟨10431914101527359763526495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13909218802036479684701993 10431914101527359763526495)
      ·
        refine ⟨15647871152291039645289743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431914101527359763526495 15647871152291039645289743)
        ·
          refine ⟨23471806728436559467934615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15647871152291039645289743 23471806728436559467934615)
          ·
            refine ⟨35207710092654839201901923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23471806728436559467934615 35207710092654839201901923)
            ·
              refine ⟨52811565138982258802852885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35207710092654839201901923 52811565138982258802852885)
              ·
                refine ⟨2475542115889793381383729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52811565138982258802852885 2475542115889793381383729)
                ·
                  refine ⟨1856656586917345036037797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2475542115889793381383729 1856656586917345036037797)
                  ·
                    refine ⟨348123110047002194257087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1856656586917345036037797 348123110047002194257087)
                    ·
                      rfl

theorem cell23_2033902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2033902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033902 prefixEnd_2033902 := by exact prefixLift 2033902
  have htrace : WordTrace (prefixWord ++ tailWord_2033902) baseStart_2033902 baseEnd_2033902 := by
    simpa [prefixWord, tailWord_2033902, baseEnd_2033902] using wordTrace_append hprefix tailTrace_2033902
  have hstable : (prefixWord ++ tailWord_2033902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033902).length < 2 ^ (prefixWord ++ tailWord_2033902).sum := by decide
  have hdescent : baseEnd_2033902 < baseStart_2033902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033922 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2033922 : Nat := 118140960795 + 2033922 * 2 ^ 59
def prefixEnd_2033922 : Nat := 4983230072969 + 3 ^ 40 * 2033922 * 2
def baseEnd_2033922 : Nat := 1044379599754096504521169

theorem tailTrace_2033922 : CollatzResearch.WordTrace tailWord_2033922 prefixEnd_2033922 1044379599754096504521169 := by
  unfold tailWord_2033922
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545807434363858766868005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49455486491636956711648013 18545807434363858766868005)
  ·
    refine ⟨3477338893943223518787751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18545807434363858766868005 3477338893943223518787751)
    ·
      refine ⟨5216008340914835278181627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477338893943223518787751 5216008340914835278181627)
      ·
        refine ⟨7824012511372252917272441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5216008340914835278181627 7824012511372252917272441)
        ·
          refine ⟨5868009383529189687954331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7824012511372252917272441 5868009383529189687954331)
          ·
            refine ⟨8802014075293784531931497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868009383529189687954331 8802014075293784531931497)
            ·
              refine ⟨6601510556470338398948623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802014075293784531931497 6601510556470338398948623)
              ·
                refine ⟨9902265834705507598422935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601510556470338398948623 9902265834705507598422935)
                ·
                  refine ⟨14853398752058261397634403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9902265834705507598422935 14853398752058261397634403)
                  ·
                    refine ⟨22280098128087392096451605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14853398752058261397634403 22280098128087392096451605)
                    ·
                      refine ⟨1044379599754096504521169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22280098128087392096451605 1044379599754096504521169)
                      ·
                        rfl

theorem cell23_2033922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2033922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033922 prefixEnd_2033922 := by exact prefixLift 2033922
  have htrace : WordTrace (prefixWord ++ tailWord_2033922) baseStart_2033922 baseEnd_2033922 := by
    simpa [prefixWord, tailWord_2033922, baseEnd_2033922] using wordTrace_append hprefix tailTrace_2033922
  have hstable : (prefixWord ++ tailWord_2033922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033922).length < 2 ^ (prefixWord ++ tailWord_2033922).sum := by decide
  have hdescent : baseEnd_2033922 < baseStart_2033922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033929 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_2033929 : Nat := 118140960795 + 2033929 * 2 ^ 59
def prefixEnd_2033929 : Nat := 4983230072969 + 3 ^ 40 * 2033929 * 2
def baseEnd_2033929 : Nat := 1044383194118677977133637

theorem tailTrace_2033929 : CollatzResearch.WordTrace tailWord_2033929 prefixEnd_2033929 1044383194118677977133637 := by
  unfold tailWord_2033929
  simp only [CollatzResearch.WordTrace]
  refine ⟨74183485048430075262976841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49455656698953383508651227 74183485048430075262976841)
  ·
    refine ⟨55637613786322556447232631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74183485048430075262976841 55637613786322556447232631)
    ·
      refine ⟨83456420679483834670848947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55637613786322556447232631 83456420679483834670848947)
      ·
        refine ⟨125184631019225752006273421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83456420679483834670848947 125184631019225752006273421)
        ·
          refine ⟨46944236632209657002352533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125184631019225752006273421 46944236632209657002352533)
          ·
            refine ⟨2200511092134827671985275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46944236632209657002352533 2200511092134827671985275)
            ·
              refine ⟨3300766638202241507977913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200511092134827671985275 3300766638202241507977913)
              ·
                refine ⟨2475574978651681130983435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300766638202241507977913 2475574978651681130983435)
                ·
                  refine ⟨3713362467977521696475153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475574978651681130983435 3713362467977521696475153)
                  ·
                    refine ⟨2785021850983141272356365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713362467977521696475153 2785021850983141272356365)
                    ·
                      refine ⟨1044383194118677977133637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785021850983141272356365 1044383194118677977133637)
                      ·
                        rfl

theorem cell23_2033929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_2033929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033929 prefixEnd_2033929 := by exact prefixLift 2033929
  have htrace : WordTrace (prefixWord ++ tailWord_2033929) baseStart_2033929 baseEnd_2033929 := by
    simpa [prefixWord, tailWord_2033929, baseEnd_2033929] using wordTrace_append hprefix tailTrace_2033929
  have hstable : (prefixWord ++ tailWord_2033929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033929).length < 2 ^ (prefixWord ++ tailWord_2033929).sum := by decide
  have hdescent : baseEnd_2033929 < baseStart_2033929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033946 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_2033946 : Nat := 118140960795 + 2033946 * 2 ^ 59
def prefixEnd_2033946 : Nat := 4983230072969 + 3 ^ 40 * 2033946 * 2
def baseEnd_2033946 : Nat := 1044391923289804410621059

theorem tailTrace_2033946 : CollatzResearch.WordTrace tailWord_2033946 prefixEnd_2033946 1044391923289804410621059 := by
  unfold tailWord_2033946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18546026272342121791586423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49456070059578991444230461 18546026272342121791586423)
  ·
    refine ⟨27819039408513182687379635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18546026272342121791586423 27819039408513182687379635)
    ·
      refine ⟨41728559112769774031069453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819039408513182687379635 41728559112769774031069453)
      ·
        refine ⟨15648209667288665261651045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41728559112769774031069453 15648209667288665261651045)
        ·
          refine ⟨2934039312616624736559571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15648209667288665261651045 2934039312616624736559571)
          ·
            refine ⟨4401058968924937104839357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934039312616624736559571 4401058968924937104839357)
            ·
              refine ⟨1650397113346851414314759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4401058968924937104839357 1650397113346851414314759)
              ·
                refine ⟨2475595670020277121472139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650397113346851414314759 2475595670020277121472139)
                ·
                  refine ⟨3713393505030415682208209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475595670020277121472139 3713393505030415682208209)
                  ·
                    refine ⟨2785045128772811761656157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713393505030415682208209 2785045128772811761656157)
                    ·
                      refine ⟨1044391923289804410621059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785045128772811761656157 1044391923289804410621059)
                      ·
                        rfl

theorem cell23_2033946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_2033946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033946 prefixEnd_2033946 := by exact prefixLift 2033946
  have htrace : WordTrace (prefixWord ++ tailWord_2033946) baseStart_2033946 baseEnd_2033946 := by
    simpa [prefixWord, tailWord_2033946, baseEnd_2033946] using wordTrace_append hprefix tailTrace_2033946
  have hstable : (prefixWord ++ tailWord_2033946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033946).length < 2 ^ (prefixWord ++ tailWord_2033946).sum := by decide
  have hdescent : baseEnd_2033946 < baseStart_2033946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2033966 : List Nat := [4, 1, 3, 3, 2, 1, 1, 8]
def baseStart_2033966 : Nat := 118140960795 + 2033966 * 2 ^ 59
def prefixEnd_2033966 : Nat := 4983230072969 + 3 ^ 40 * 2033966 * 2
def baseEnd_2033966 : Nat := 38681562700107197495221

theorem tailTrace_2033966 : CollatzResearch.WordTrace tailWord_2033966 prefixEnd_2033966 38681562700107197495221 := by
  unfold tailWord_2033966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273104318662003822759219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49456556366197353721382501 9273104318662003822759219)
  ·
    refine ⟨13909656477993005734138829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273104318662003822759219 13909656477993005734138829)
    ·
      refine ⟨5216121179247377150302061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13909656477993005734138829 5216121179247377150302061)
      ·
        refine ⟨1956045442217766431363273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5216121179247377150302061 1956045442217766431363273)
        ·
          refine ⟨1467034081663324823522455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1956045442217766431363273 1467034081663324823522455)
          ·
            refine ⟨2200551122494987235283683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467034081663324823522455 2200551122494987235283683)
            ·
              refine ⟨3300826683742480852925525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200551122494987235283683 3300826683742480852925525)
              ·
                refine ⟨38681562700107197495221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3300826683742480852925525 38681562700107197495221)
                ·
                  rfl

theorem cell23_2033966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_2033966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2033966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2033966 prefixEnd_2033966 := by exact prefixLift 2033966
  have htrace : WordTrace (prefixWord ++ tailWord_2033966) baseStart_2033966 baseEnd_2033966 := by
    simpa [prefixWord, tailWord_2033966, baseEnd_2033966] using wordTrace_append hprefix tailTrace_2033966
  have hstable : (prefixWord ++ tailWord_2033966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2033966).length < 2 ^ (prefixWord ++ tailWord_2033966).sum := by decide
  have hdescent : baseEnd_2033966 < baseStart_2033966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2033966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034016 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2]
def baseStart_2034016 : Nat := 118140960795 + 2034016 * 2 ^ 59
def prefixEnd_2034016 : Nat := 4983230072969 + 3 ^ 40 * 2034016 * 2
def baseEnd_2034016 : Nat := 1044427866935619136745737

theorem tailTrace_2034016 : CollatzResearch.WordTrace tailWord_2034016 prefixEnd_2034016 1044427866935619136745737 := by
  unfold tailWord_2034016
  simp only [CollatzResearch.WordTrace]
  refine ⟨37093329099557444560696951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49457772132743259414262601 37093329099557444560696951)
  ·
    refine ⟨55639993649336166841045427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37093329099557444560696951 55639993649336166841045427)
    ·
      refine ⟨83459990474004250261568141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55639993649336166841045427 83459990474004250261568141)
      ·
        refine ⟨31297496427751593848088053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83459990474004250261568141 31297496427751593848088053)
        ·
          refine ⟨2934140290101711923258255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31297496427751593848088053 2934140290101711923258255)
          ·
            refine ⟨4401210435152567884887383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2934140290101711923258255 4401210435152567884887383)
            ·
              refine ⟨6601815652728851827331075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401210435152567884887383 6601815652728851827331075)
              ·
                refine ⟨9902723479093277740996613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601815652728851827331075 9902723479093277740996613)
                ·
                  refine ⟨1856760652329989576436865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9902723479093277740996613 1856760652329989576436865)
                  ·
                    refine ⟨1392570489247492182327649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856760652329989576436865 1392570489247492182327649)
                    ·
                      refine ⟨1044427866935619136745737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392570489247492182327649 1044427866935619136745737)
                      ·
                        rfl

theorem cell23_2034016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_2034016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034016 prefixEnd_2034016 := by exact prefixLift 2034016
  have htrace : WordTrace (prefixWord ++ tailWord_2034016) baseStart_2034016 baseEnd_2034016 := by
    simpa [prefixWord, tailWord_2034016, baseEnd_2034016] using wordTrace_append hprefix tailTrace_2034016
  have hstable : (prefixWord ++ tailWord_2034016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034016).length < 2 ^ (prefixWord ++ tailWord_2034016).sum := by decide
  have hdescent : baseEnd_2034016 < baseStart_2034016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034032 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_2034032 : Nat := 118140960795 + 2034032 * 2 ^ 59
def prefixEnd_2034032 : Nat := 4983230072969 + 3 ^ 40 * 2034032 * 2
def baseEnd_2034032 : Nat := 1044436082626091074145663

theorem tailTrace_2034032 : CollatzResearch.WordTrace tailWord_2034032 prefixEnd_2034032 1044436082626091074145663 := by
  unfold tailWord_2034032
  simp only [CollatzResearch.WordTrace]
  refine ⟨37093620883528461926988175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49458161178037949235984233 37093620883528461926988175)
  ·
    refine ⟨55640431325292692890482263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37093620883528461926988175 55640431325292692890482263)
    ·
      refine ⟨83460646987939039335723395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55640431325292692890482263 83460646987939039335723395)
      ·
        refine ⟨125190970481908559003585093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83460646987939039335723395 125190970481908559003585093)
        ·
          refine ⟨23473306965357854813172205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125190970481908559003585093 23473306965357854813172205)
          ·
            refine ⟨8802490112009195554939577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23473306965357854813172205 8802490112009195554939577)
            ·
              refine ⟨6601867584006896666204683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802490112009195554939577 6601867584006896666204683)
              ·
                refine ⟨9902801376010344999307025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601867584006896666204683 9902801376010344999307025)
                ·
                  refine ⟨7427101032007758749480269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902801376010344999307025 7427101032007758749480269)
                  ·
                    refine ⟨2785162887002909531055101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7427101032007758749480269 2785162887002909531055101)
                    ·
                      refine ⟨1044436082626091074145663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785162887002909531055101 1044436082626091074145663)
                      ·
                        rfl

theorem cell23_2034032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_2034032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034032 prefixEnd_2034032 := by exact prefixLift 2034032
  have htrace : WordTrace (prefixWord ++ tailWord_2034032) baseStart_2034032 baseEnd_2034032 := by
    simpa [prefixWord, tailWord_2034032, baseEnd_2034032] using wordTrace_append hprefix tailTrace_2034032
  have hstable : (prefixWord ++ tailWord_2034032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034032).length < 2 ^ (prefixWord ++ tailWord_2034032).sum := by decide
  have hdescent : baseEnd_2034032 < baseStart_2034032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034035 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 4, 5]
def baseStart_2034035 : Nat := 118140960795 + 2034035 * 2 ^ 59
def prefixEnd_2034035 : Nat := 4983230072969 + 3 ^ 40 * 2034035 * 2
def baseEnd_2034035 : Nat := 348145874356018187469383

theorem tailTrace_2034035 : CollatzResearch.WordTrace tailWord_2034035 prefixEnd_2034035 348145874356018187469383 := by
  unfold tailWord_2034035
  simp only [CollatzResearch.WordTrace]
  refine ⟨74187351186046055366335559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49458234124030703577557039 74187351186046055366335559)
  ·
    refine ⟨111281026779069083049503339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74187351186046055366335559 111281026779069083049503339)
    ·
      refine ⟨166921540168603624574255009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111281026779069083049503339 166921540168603624574255009)
      ·
        refine ⟨125191155126452718430691257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166921540168603624574255009 125191155126452718430691257)
        ·
          refine ⟨93893366344839538823018443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125191155126452718430691257 93893366344839538823018443)
          ·
            refine ⟨140840049517259308234527665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93893366344839538823018443 140840049517259308234527665)
            ·
              refine ⟨105630037137944481175895749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140840049517259308234527665 105630037137944481175895749)
              ·
                refine ⟨19805631963364590220480453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105630037137944481175895749 19805631963364590220480453)
                ·
                  refine ⟨3713555993130860666340085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19805631963364590220480453 3713555993130860666340085)
                  ·
                    refine ⟨348145874356018187469383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3713555993130860666340085 348145874356018187469383)
                    ·
                      rfl

theorem cell23_2034035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 5].length) (baseStart_2034035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034035 prefixEnd_2034035 := by exact prefixLift 2034035
  have htrace : WordTrace (prefixWord ++ tailWord_2034035) baseStart_2034035 baseEnd_2034035 := by
    simpa [prefixWord, tailWord_2034035, baseEnd_2034035] using wordTrace_append hprefix tailTrace_2034035
  have hstable : (prefixWord ++ tailWord_2034035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034035).length < 2 ^ (prefixWord ++ tailWord_2034035).sum := by decide
  have hdescent : baseEnd_2034035 < baseStart_2034035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034052 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2034052 : Nat := 118140960795 + 2034052 * 2 ^ 59
def prefixEnd_2034052 : Nat := 4983230072969 + 3 ^ 40 * 2034052 * 2
def baseEnd_2034052 : Nat := 348148784079726998631857

theorem tailTrace_2034052 : CollatzResearch.WordTrace tailWord_2034052 prefixEnd_2034052 348148784079726998631857 := by
  unfold tailWord_2034052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37093985613492233634852205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49458647484656311513136273 37093985613492233634852205)
  ·
    refine ⟨13910244605059587613069577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37093985613492233634852205 13910244605059587613069577)
    ·
      refine ⟨10432683453794690709802183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13910244605059587613069577 10432683453794690709802183)
      ·
        refine ⟨15649025180692036064703275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432683453794690709802183 15649025180692036064703275)
        ·
          refine ⟨23473537771038054097054913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15649025180692036064703275 23473537771038054097054913)
          ·
            refine ⟨17605153328278540572791185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23473537771038054097054913 17605153328278540572791185)
            ·
              refine ⟨13203864996208905429593389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17605153328278540572791185 13203864996208905429593389)
              ·
                refine ⟨4951449373578339536097521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13203864996208905429593389 4951449373578339536097521)
                ·
                  refine ⟨3713587030183754652073141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951449373578339536097521 3713587030183754652073141)
                  ·
                    refine ⟨348148784079726998631857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3713587030183754652073141 348148784079726998631857)
                    ·
                      rfl

theorem cell23_2034052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2034052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034052 prefixEnd_2034052 := by exact prefixLift 2034052
  have htrace : WordTrace (prefixWord ++ tailWord_2034052) baseStart_2034052 baseEnd_2034052 := by
    simpa [prefixWord, tailWord_2034052, baseEnd_2034052] using wordTrace_append hprefix tailTrace_2034052
  have hstable : (prefixWord ++ tailWord_2034052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034052).length < 2 ^ (prefixWord ++ tailWord_2034052).sum := by decide
  have hdescent : baseEnd_2034052 < baseStart_2034052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034092 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_2034092 : Nat := 118140960795 + 2034092 * 2 ^ 59
def prefixEnd_2034092 : Nat := 4983230072969 + 3 ^ 40 * 2034092 * 2
def baseEnd_2034092 : Nat := 1044466891465360839395387

theorem tailTrace_2034092 : CollatzResearch.WordTrace tailWord_2034092 prefixEnd_2034092 1044466891465360839395387 := by
  unfold tailWord_2034092
  simp only [CollatzResearch.WordTrace]
  refine ⟨37094715073419777050580265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49459620097893036067440353 37094715073419777050580265)
  ·
    refine ⟨27821036305064832787935199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37094715073419777050580265 27821036305064832787935199)
    ·
      refine ⟨41731554457597249181902799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27821036305064832787935199 41731554457597249181902799)
      ·
        refine ⟨62597331686395873772854199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41731554457597249181902799 62597331686395873772854199)
        ·
          refine ⟨93895997529593810659281299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62597331686395873772854199 93895997529593810659281299)
          ·
            refine ⟨140843996294390715988921949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93895997529593810659281299 140843996294390715988921949)
            ·
              refine ⟨52816498610396518495845731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140843996294390715988921949 52816498610396518495845731)
              ·
                refine ⟨79224747915594777743768597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52816498610396518495845731 79224747915594777743768597)
                ·
                  refine ⟨3713660058543505206739153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79224747915594777743768597 3713660058543505206739153)
                  ·
                    refine ⟨2785245043907628905054365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713660058543505206739153 2785245043907628905054365)
                    ·
                      refine ⟨1044466891465360839395387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785245043907628905054365 1044466891465360839395387)
                      ·
                        rfl

theorem cell23_2034092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_2034092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034092 prefixEnd_2034092 := by exact prefixLift 2034092
  have htrace : WordTrace (prefixWord ++ tailWord_2034092) baseStart_2034092 baseEnd_2034092 := by
    simpa [prefixWord, tailWord_2034092, baseEnd_2034092] using wordTrace_append hprefix tailTrace_2034092
  have hstable : (prefixWord ++ tailWord_2034092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034092).length < 2 ^ (prefixWord ++ tailWord_2034092).sum := by decide
  have hdescent : baseEnd_2034092 < baseStart_2034092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034109 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2034109 : Nat := 118140960795 + 2034109 * 2 ^ 59
def prefixEnd_2034109 : Nat := 4983230072969 + 3 ^ 40 * 2034109 * 2
def baseEnd_2034109 : Nat := 1044475620636487272882809

theorem tailTrace_2034109 : CollatzResearch.WordTrace tailWord_2034109 prefixEnd_2034109 1044475620636487272882809 := by
  unfold tailWord_2034109
  simp only [CollatzResearch.WordTrace]
  refine ⟨74190050187777966004529381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49460033458518644003019587 74190050187777966004529381)
  ·
    refine ⟨13910634410208368625849259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74190050187777966004529381 13910634410208368625849259)
    ·
      refine ⟨20865951615312552938773889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910634410208368625849259 20865951615312552938773889)
      ·
        refine ⟨15649463711484414704080417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20865951615312552938773889 15649463711484414704080417)
        ·
          refine ⟨11737097783613311028060313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15649463711484414704080417 11737097783613311028060313)
          ·
            refine ⟨8802823337709983271045235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11737097783613311028060313 8802823337709983271045235)
            ·
              refine ⟨13204235006564974906567853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8802823337709983271045235 13204235006564974906567853)
              ·
                refine ⟨4951588127461865589962945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13204235006564974906567853 4951588127461865589962945)
                ·
                  refine ⟨3713691095596399192472209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951588127461865589962945 3713691095596399192472209)
                  ·
                    refine ⟨2785268321697299394354157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713691095596399192472209 2785268321697299394354157)
                    ·
                      refine ⟨1044475620636487272882809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785268321697299394354157 1044475620636487272882809)
                      ·
                        rfl

theorem cell23_2034109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2034109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034109 prefixEnd_2034109 := by exact prefixLift 2034109
  have htrace : WordTrace (prefixWord ++ tailWord_2034109) baseStart_2034109 baseEnd_2034109 := by
    simpa [prefixWord, tailWord_2034109, baseEnd_2034109] using wordTrace_append hprefix tailTrace_2034109
  have hstable : (prefixWord ++ tailWord_2034109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034109).length < 2 ^ (prefixWord ++ tailWord_2034109).sum := by decide
  have hdescent : baseEnd_2034109 < baseStart_2034109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034115 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_2034115 : Nat := 118140960795 + 2034115 * 2 ^ 59
def prefixEnd_2034115 : Nat := 4983230072969 + 3 ^ 40 * 2034115 * 2
def baseEnd_2034115 : Nat := 1044478701520414249407781

theorem tailTrace_2034115 : CollatzResearch.WordTrace tailWord_2034115 prefixEnd_2034115 1044478701520414249407781 := by
  unfold tailWord_2034115
  simp only [CollatzResearch.WordTrace]
  refine ⟨74190269025756229029247799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49460179350504152686165199 74190269025756229029247799)
  ·
    refine ⟨111285403538634343543871699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74190269025756229029247799 111285403538634343543871699)
    ·
      refine ⟨166928105307951515315807549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111285403538634343543871699 166928105307951515315807549)
      ·
        refine ⟨62598039490481818243427831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166928105307951515315807549 62598039490481818243427831)
        ·
          refine ⟨93897059235722727365141747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62598039490481818243427831 93897059235722727365141747)
          ·
            refine ⟨140845588853584091047712621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93897059235722727365141747 140845588853584091047712621)
            ·
              refine ⟨52817095820094034142892233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140845588853584091047712621 52817095820094034142892233)
              ·
                refine ⟨39612821865070525607169175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52817095820094034142892233 39612821865070525607169175)
                ·
                  refine ⟨59419232797605788410753763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39612821865070525607169175 59419232797605788410753763)
                  ·
                    refine ⟨89128849196408682616130645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59419232797605788410753763 89128849196408682616130645)
                    ·
                      refine ⟨1044478701520414249407781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 89128849196408682616130645 1044478701520414249407781)
                      ·
                        rfl

theorem cell23_2034115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_2034115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034115 prefixEnd_2034115 := by exact prefixLift 2034115
  have htrace : WordTrace (prefixWord ++ tailWord_2034115) baseStart_2034115 baseEnd_2034115 := by
    simpa [prefixWord, tailWord_2034115, baseEnd_2034115] using wordTrace_append hprefix tailTrace_2034115
  have hstable : (prefixWord ++ tailWord_2034115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034115).length < 2 ^ (prefixWord ++ tailWord_2034115).sum := by decide
  have hdescent : baseEnd_2034115 < baseStart_2034115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034133 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2034133 : Nat := 118140960795 + 2034133 * 2 ^ 59
def prefixEnd_2034133 : Nat := 4983230072969 + 3 ^ 40 * 2034133 * 2
def baseEnd_2034133 : Nat := 348162648057398392994233

theorem tailTrace_2034133 : CollatzResearch.WordTrace tailWord_2034133 prefixEnd_2034133 348162648057398392994233 := by
  unfold tailWord_2034133
  simp only [CollatzResearch.WordTrace]
  refine ⟨74190925539691018103403053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49460617026460678735602035 74190925539691018103403053)
  ·
    refine ⟨27821597077384131788776145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74190925539691018103403053 27821597077384131788776145)
    ·
      refine ⟨20866197808038098841582109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27821597077384131788776145 20866197808038098841582109)
      ·
        refine ⟨7824824178014287065593291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20866197808038098841582109 7824824178014287065593291)
        ·
          refine ⟨11737236267021430598389937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824824178014287065593291 11737236267021430598389937)
          ·
            refine ⟨8802927200266072948792453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11737236267021430598389937 8802927200266072948792453)
            ·
              refine ⟨1650548850049888677898585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8802927200266072948792453 1650548850049888677898585)
              ·
                refine ⟨1237911637537416508423939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650548850049888677898585 1237911637537416508423939)
                ·
                  refine ⟨1856867456306124762635909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237911637537416508423939 1856867456306124762635909)
                  ·
                    refine ⟨348162648057398392994233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1856867456306124762635909 348162648057398392994233)
                    ·
                      rfl

theorem cell23_2034133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2034133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034133 prefixEnd_2034133 := by exact prefixLift 2034133
  have htrace : WordTrace (prefixWord ++ tailWord_2034133) baseStart_2034133 baseEnd_2034133 := by
    simpa [prefixWord, tailWord_2034133, baseEnd_2034133] using wordTrace_append hprefix tailTrace_2034133
  have hstable : (prefixWord ++ tailWord_2034133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034133).length < 2 ^ (prefixWord ++ tailWord_2034133).sum := by decide
  have hdescent : baseEnd_2034133 < baseStart_2034133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034166 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_2034166 : Nat := 118140960795 + 2034166 * 2 ^ 59
def prefixEnd_2034166 : Nat := 4983230072969 + 3 ^ 40 * 2034166 * 2
def baseEnd_2034166 : Nat := 1044504889033793549870047

theorem tailTrace_2034166 : CollatzResearch.WordTrace tailWord_2034166 prefixEnd_2034166 1044504889033793549870047 := by
  unfold tailWord_2034166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637008071785716546209647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49461419432380976492902901 4637008071785716546209647)
  ·
    refine ⟨6955512107678574819314471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637008071785716546209647 6955512107678574819314471)
    ·
      refine ⟨10433268161517862228971707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955512107678574819314471 10433268161517862228971707)
      ·
        refine ⟨15649902242276793343457561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433268161517862228971707 15649902242276793343457561)
        ·
          refine ⟨11737426681707595007593171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15649902242276793343457561 11737426681707595007593171)
          ·
            refine ⟨17606140022561392511389757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737426681707595007593171 17606140022561392511389757)
            ·
              refine ⟨6602302508460522191771159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17606140022561392511389757 6602302508460522191771159)
              ·
                refine ⟨9903453762690783287656739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6602302508460522191771159 9903453762690783287656739)
                ·
                  refine ⟨14855180644036174931485109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9903453762690783287656739 14855180644036174931485109)
                  ·
                    refine ⟨1392673185378391399826729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14855180644036174931485109 1392673185378391399826729)
                    ·
                      refine ⟨1044504889033793549870047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392673185378391399826729 1044504889033793549870047)
                      ·
                        rfl

theorem cell23_2034166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_2034166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034166 prefixEnd_2034166 := by exact prefixLift 2034166
  have htrace : WordTrace (prefixWord ++ tailWord_2034166) baseStart_2034166 baseEnd_2034166 := by
    simpa [prefixWord, tailWord_2034166, baseEnd_2034166] using wordTrace_append hprefix tailTrace_2034166
  have hstable : (prefixWord ++ tailWord_2034166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034166).length < 2 ^ (prefixWord ++ tailWord_2034166).sum := by decide
  have hdescent : baseEnd_2034166 < baseStart_2034166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034173 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_2034173 : Nat := 118140960795 + 2034173 * 2 ^ 59
def prefixEnd_2034173 : Nat := 4983230072969 + 3 ^ 40 * 2034173 * 2
def baseEnd_2034173 : Nat := 1044508483398375022482515

theorem tailTrace_2034173 : CollatzResearch.WordTrace tailWord_2034173 prefixEnd_2034173 1044508483398375022482515 := by
  unfold tailWord_2034173
  simp only [CollatzResearch.WordTrace]
  refine ⟨74192384459546104934859173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49461589639697403289906115 74192384459546104934859173)
  ·
    refine ⟨13911072086164894675286095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74192384459546104934859173 13911072086164894675286095)
    ·
      refine ⟨20866608129247342012929143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13911072086164894675286095 20866608129247342012929143)
      ·
        refine ⟨31299912193871013019393715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20866608129247342012929143 31299912193871013019393715)
        ·
          refine ⟨46949868290806519529090573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31299912193871013019393715 46949868290806519529090573)
          ·
            refine ⟨17606200609052444823408965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46949868290806519529090573 17606200609052444823408965)
            ·
              refine ⟨3301162614197333404389181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17606200609052444823408965 3301162614197333404389181)
              ·
                refine ⟨1237935980324000026645943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3301162614197333404389181 1237935980324000026645943)
                ·
                  refine ⟨1856903970486000039968915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237935980324000026645943 1856903970486000039968915)
                  ·
                    refine ⟨2785355955729000059953373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1856903970486000039968915 2785355955729000059953373)
                    ·
                      refine ⟨1044508483398375022482515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785355955729000059953373 1044508483398375022482515)
                      ·
                        rfl

theorem cell23_2034173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_2034173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034173 prefixEnd_2034173 := by exact prefixLift 2034173
  have htrace : WordTrace (prefixWord ++ tailWord_2034173) baseStart_2034173 baseEnd_2034173 := by
    simpa [prefixWord, tailWord_2034173, baseEnd_2034173] using wordTrace_append hprefix tailTrace_2034173
  have hstable : (prefixWord ++ tailWord_2034173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034173).length < 2 ^ (prefixWord ++ tailWord_2034173).sum := by decide
  have hdescent : baseEnd_2034173 < baseStart_2034173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034179 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 4]
def baseStart_2034179 : Nat := 118140960795 + 2034179 * 2 ^ 59
def prefixEnd_2034179 : Nat := 4983230072969 + 3 ^ 40 * 2034179 * 2
def baseEnd_2034179 : Nat := 1044511564282301999007487

theorem tailTrace_2034179 : CollatzResearch.WordTrace tailWord_2034179 prefixEnd_2034179 1044511564282301999007487 := by
  unfold tailWord_2034179
  simp only [CollatzResearch.WordTrace]
  refine ⟨74192603297524367959577591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49461735531682911973051727 74192603297524367959577591)
  ·
    refine ⟨111288904946286551939366387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74192603297524367959577591 111288904946286551939366387)
    ·
      refine ⟨166933357419429827909049581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111288904946286551939366387 166933357419429827909049581)
      ·
        refine ⟨62600009032286185465893593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166933357419429827909049581 62600009032286185465893593)
        ·
          refine ⟨46950006774214639099420195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62600009032286185465893593 46950006774214639099420195)
          ·
            refine ⟨70425010161321958649130293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46950006774214639099420195 70425010161321958649130293)
            ·
              refine ⟨6602344702623933623355965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70425010161321958649130293 6602344702623933623355965)
              ·
                refine ⟨2475879263483975108758487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6602344702623933623355965 2475879263483975108758487)
                ·
                  refine ⟨3713818895225962663137731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475879263483975108758487 3713818895225962663137731)
                  ·
                    refine ⟨5570728342838943994706597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713818895225962663137731 5570728342838943994706597)
                    ·
                      refine ⟨1044511564282301999007487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5570728342838943994706597 1044511564282301999007487)
                      ·
                        rfl

theorem cell23_2034179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_2034179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034179 prefixEnd_2034179 := by exact prefixLift 2034179
  have htrace : WordTrace (prefixWord ++ tailWord_2034179) baseStart_2034179 baseEnd_2034179 := by
    simpa [prefixWord, tailWord_2034179, baseEnd_2034179] using wordTrace_append hprefix tailTrace_2034179
  have hstable : (prefixWord ++ tailWord_2034179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034179).length < 2 ^ (prefixWord ++ tailWord_2034179).sum := by decide
  have hdescent : baseEnd_2034179 < baseStart_2034179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034229 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2034229 : Nat := 118140960795 + 2034229 * 2 ^ 59
def prefixEnd_2034229 : Nat := 4983230072969 + 3 ^ 40 * 2034229 * 2
def baseEnd_2034229 : Nat := 1044537238315026803382257

theorem tailTrace_2034229 : CollatzResearch.WordTrace tailWord_2034229 prefixEnd_2034229 1044537238315026803382257 := by
  unfold tailWord_2034229
  simp only [CollatzResearch.WordTrace]
  refine ⟨74194426947343226498897741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49462951298228817665931827 74194426947343226498897741)
  ·
    refine ⟨27822910105253709937086653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74194426947343226498897741 27822910105253709937086653)
    ·
      refine ⟨10433591289470141226407495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27822910105253709937086653 10433591289470141226407495)
      ·
        refine ⟨15650386934205211839611243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433591289470141226407495 15650386934205211839611243)
        ·
          refine ⟨23475580401307817759416865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15650386934205211839611243 23475580401307817759416865)
          ·
            refine ⟨17606685300980863319562649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23475580401307817759416865 17606685300980863319562649)
            ·
              refine ⟨13205013975735647489671987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17606685300980863319562649 13205013975735647489671987)
              ·
                refine ⟨19807520963603471234507981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13205013975735647489671987 19807520963603471234507981)
                ·
                  refine ⟨7427820361351301712940493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19807520963603471234507981 7427820361351301712940493)
                  ·
                    refine ⟨2785432635506738142352685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7427820361351301712940493 2785432635506738142352685)
                    ·
                      refine ⟨1044537238315026803382257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785432635506738142352685 1044537238315026803382257)
                      ·
                        rfl

theorem cell23_2034229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2034229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034229 prefixEnd_2034229 := by exact prefixLift 2034229
  have htrace : WordTrace (prefixWord ++ tailWord_2034229) baseStart_2034229 baseEnd_2034229 := by
    simpa [prefixWord, tailWord_2034229, baseEnd_2034229] using wordTrace_append hprefix tailTrace_2034229
  have hstable : (prefixWord ++ tailWord_2034229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034229).length < 2 ^ (prefixWord ++ tailWord_2034229).sum := by decide
  have hdescent : baseEnd_2034229 < baseStart_2034229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034247 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_2034247 : Nat := 118140960795 + 2034247 * 2 ^ 59
def prefixEnd_2034247 : Nat := 4983230072969 + 3 ^ 40 * 2034247 * 2
def baseEnd_2034247 : Nat := 1044546480966807732957175

theorem tailTrace_2034247 : CollatzResearch.WordTrace tailWord_2034247 prefixEnd_2034247 1044546480966807732957175 := by
  unfold tailWord_2034247
  simp only [CollatzResearch.WordTrace]
  refine ⟨74195083461278015573052995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49463388974185343715368663 74195083461278015573052995)
  ·
    refine ⟨111292625191917023359579493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74195083461278015573052995 111292625191917023359579493)
    ·
      refine ⟨20867367223484441879921155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111292625191917023359579493 20867367223484441879921155)
      ·
        refine ⟨31301050835226662819881733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20867367223484441879921155 31301050835226662819881733)
        ·
          refine ⟨5868947031604999278727825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31301050835226662819881733 5868947031604999278727825)
          ·
            refine ⟨4401710273703749459045869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5868947031604999278727825 4401710273703749459045869)
            ·
              refine ⟨1650641352638906047142201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4401710273703749459045869 1650641352638906047142201)
              ·
                refine ⟨1237981014479179535356651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650641352638906047142201 1237981014479179535356651)
                ·
                  refine ⟨1856971521718769303034977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237981014479179535356651 1856971521718769303034977)
                  ·
                    refine ⟨1392728641289076977276233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856971521718769303034977 1392728641289076977276233)
                    ·
                      refine ⟨1044546480966807732957175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392728641289076977276233 1044546480966807732957175)
                      ·
                        rfl

theorem cell23_2034247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_2034247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034247 prefixEnd_2034247 := by exact prefixLift 2034247
  have htrace : WordTrace (prefixWord ++ tailWord_2034247) baseStart_2034247 baseEnd_2034247 := by
    simpa [prefixWord, tailWord_2034247, baseEnd_2034247] using wordTrace_append hprefix tailTrace_2034247
  have hstable : (prefixWord ++ tailWord_2034247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034247).length < 2 ^ (prefixWord ++ tailWord_2034247).sum := by decide
  have hdescent : baseEnd_2034247 < baseStart_2034247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034273 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_2034273 : Nat := 118140960795 + 2034273 * 2 ^ 59
def prefixEnd_2034273 : Nat := 4983230072969 + 3 ^ 40 * 2034273 * 2
def baseEnd_2034273 : Nat := 1044559831463824631232055

theorem tailTrace_2034273 : CollatzResearch.WordTrace tailWord_2034273 prefixEnd_2034273 1044559831463824631232055 := by
  unfold tailWord_2034273
  simp only [CollatzResearch.WordTrace]
  refine ⟨74196031759183822013499473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49464021172789214675666315 74196031759183822013499473)
  ·
    refine ⟨55647023819387866510124605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74196031759183822013499473 55647023819387866510124605)
    ·
      refine ⟨20867633932270449941296727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55647023819387866510124605 20867633932270449941296727)
      ·
        refine ⟨31301450898405674911945091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20867633932270449941296727 31301450898405674911945091)
        ·
          refine ⟨46952176347608512367917637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31301450898405674911945091 46952176347608512367917637)
          ·
            refine ⟨8803533065176596068984557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46952176347608512367917637 8803533065176596068984557)
            ·
              refine ⟨3301324899441223525869209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8803533065176596068984557 3301324899441223525869209)
              ·
                refine ⟨2475993674580917644401907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301324899441223525869209 2475993674580917644401907)
                ·
                  refine ⟨3713990511871376466602861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475993674580917644401907 3713990511871376466602861)
                  ·
                    refine ⟨1392746441951766174976073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713990511871376466602861 1392746441951766174976073)
                    ·
                      refine ⟨1044559831463824631232055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392746441951766174976073 1044559831463824631232055)
                      ·
                        rfl

theorem cell23_2034273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_2034273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034273 prefixEnd_2034273 := by exact prefixLift 2034273
  have htrace : WordTrace (prefixWord ++ tailWord_2034273) baseStart_2034273 baseEnd_2034273 := by
    simpa [prefixWord, tailWord_2034273, baseEnd_2034273] using wordTrace_append hprefix tailTrace_2034273
  have hstable : (prefixWord ++ tailWord_2034273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034273).length < 2 ^ (prefixWord ++ tailWord_2034273).sum := by decide
  have hdescent : baseEnd_2034273 < baseStart_2034273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034319 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_2034319 : Nat := 118140960795 + 2034319 * 2 ^ 59
def prefixEnd_2034319 : Nat := 4983230072969 + 3 ^ 40 * 2034319 * 2
def baseEnd_2034319 : Nat := 1044583451573931451256843

theorem tailTrace_2034319 : CollatzResearch.WordTrace tailWord_2034319 prefixEnd_2034319 1044583451573931451256843 := by
  unfold tailWord_2034319
  simp only [CollatzResearch.WordTrace]
  refine ⟨74197709517017171869674011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49465139678011447913116007 74197709517017171869674011)
  ·
    refine ⟨111296564275525757804511017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74197709517017171869674011 111296564275525757804511017)
    ·
      refine ⟨83472423206644318353383263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111296564275525757804511017 83472423206644318353383263)
      ·
        refine ⟨125208634809966477530074895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83472423206644318353383263 125208634809966477530074895)
        ·
          refine ⟨187812952214949716295112343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125208634809966477530074895 187812952214949716295112343)
          ·
            refine ⟨281719428322424574442668515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187812952214949716295112343 281719428322424574442668515)
            ·
              refine ⟨422579142483636861664002773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281719428322424574442668515 422579142483636861664002773)
              ·
                refine ⟨9904198651960238945250065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 422579142483636861664002773 9904198651960238945250065)
                ·
                  refine ⟨7428148988970179208937549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9904198651960238945250065 7428148988970179208937549)
                  ·
                    refine ⟨2785555870863817203351581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7428148988970179208937549 2785555870863817203351581)
                    ·
                      refine ⟨1044583451573931451256843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785555870863817203351581 1044583451573931451256843)
                      ·
                        rfl

theorem cell23_2034319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_2034319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034319 prefixEnd_2034319 := by exact prefixLift 2034319
  have htrace : WordTrace (prefixWord ++ tailWord_2034319) baseStart_2034319 baseEnd_2034319 := by
    simpa [prefixWord, tailWord_2034319, baseEnd_2034319] using wordTrace_append hprefix tailTrace_2034319
  have hstable : (prefixWord ++ tailWord_2034319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034319).length < 2 ^ (prefixWord ++ tailWord_2034319).sum := by decide
  have hdescent : baseEnd_2034319 < baseStart_2034319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034339 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 2, 5]
def baseStart_2034339 : Nat := 118140960795 + 2034339 * 2 ^ 59
def prefixEnd_2034339 : Nat := 4983230072969 + 3 ^ 40 * 2034339 * 2
def baseEnd_2034339 : Nat := 348197907062340457668917

theorem tailTrace_2034339 : CollatzResearch.WordTrace tailWord_2034339 prefixEnd_2034339 348197907062340457668917 := by
  unfold tailWord_2034339
  simp only [CollatzResearch.WordTrace]
  refine ⟨74198438976944715285402071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49465625984629810190268047 74198438976944715285402071)
  ·
    refine ⟨111297658465417072928103107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74198438976944715285402071 111297658465417072928103107)
    ·
      refine ⟨166946487698125609392154661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111297658465417072928103107 166946487698125609392154661)
      ·
        refine ⟨31302466443398551761028999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166946487698125609392154661 31302466443398551761028999)
        ·
          refine ⟨46953699665097827641543499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31302466443398551761028999 46953699665097827641543499)
          ·
            refine ⟨70430549497646741462315249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46953699665097827641543499 70430549497646741462315249)
            ·
              refine ⟨52822912123235056096736437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70430549497646741462315249 52822912123235056096736437)
              ·
                refine ⟨4952148011553286509069041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52822912123235056096736437 4952148011553286509069041)
                ·
                  refine ⟨3714111008664964881801781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4952148011553286509069041 3714111008664964881801781)
                  ·
                    refine ⟨348197907062340457668917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3714111008664964881801781 348197907062340457668917)
                    ·
                      rfl

theorem cell23_2034339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 5].length) (baseStart_2034339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034339 prefixEnd_2034339 := by exact prefixLift 2034339
  have htrace : WordTrace (prefixWord ++ tailWord_2034339) baseStart_2034339 baseEnd_2034339 := by
    simpa [prefixWord, tailWord_2034339, baseEnd_2034339] using wordTrace_append hprefix tailTrace_2034339
  have hstable : (prefixWord ++ tailWord_2034339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034339).length < 2 ^ (prefixWord ++ tailWord_2034339).sum := by decide
  have hdescent : baseEnd_2034339 < baseStart_2034339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034399 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 8]
def baseStart_2034399 : Nat := 118140960795 + 2034399 * 2 ^ 59
def prefixEnd_2034399 : Nat := 4983230072969 + 3 ^ 40 * 2034399 * 2
def baseEnd_2034399 : Nat := 116069392225143459806275

theorem tailTrace_2034399 : CollatzResearch.WordTrace tailWord_2034399 prefixEnd_2034399 116069392225143459806275 := by
  unfold tailWord_2034399
  simp only [CollatzResearch.WordTrace]
  refine ⟨74200627356727345532586251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49467084904484897021724167 74200627356727345532586251)
  ·
    refine ⟨111300941035091018298879377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74200627356727345532586251 111300941035091018298879377)
    ·
      refine ⟨83475705776318263724159533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111300941035091018298879377 83475705776318263724159533)
      ·
        refine ⟨31303389666119348896559825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83475705776318263724159533 31303389666119348896559825)
        ·
          refine ⟨23477542249589511672419869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31303389666119348896559825 23477542249589511672419869)
          ·
            refine ⟨8804078343596066877157451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23477542249589511672419869 8804078343596066877157451)
            ·
              refine ⟨13206117515394100315736177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804078343596066877157451 13206117515394100315736177)
              ·
                refine ⟨9904588136545575236802133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13206117515394100315736177 9904588136545575236802133)
                ·
                  refine ⟨116069392225143459806275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9904588136545575236802133 116069392225143459806275)
                  ·
                    rfl

theorem cell23_2034399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 8].length) (baseStart_2034399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034399 prefixEnd_2034399 := by exact prefixLift 2034399
  have htrace : WordTrace (prefixWord ++ tailWord_2034399) baseStart_2034399 baseEnd_2034399 := by
    simpa [prefixWord, tailWord_2034399, baseEnd_2034399] using wordTrace_append hprefix tailTrace_2034399
  have hstable : (prefixWord ++ tailWord_2034399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034399).length < 2 ^ (prefixWord ++ tailWord_2034399).sum := by decide
  have hdescent : baseEnd_2034399 < baseStart_2034399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034413 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2034413 : Nat := 118140960795 + 2034413 * 2 ^ 59
def prefixEnd_2034413 : Nat := 4983230072969 + 3 ^ 40 * 2034413 * 2
def baseEnd_2034413 : Nat := 1044631718755454083481411

theorem tailTrace_2034413 : CollatzResearch.WordTrace tailWord_2034413 prefixEnd_2034413 1044631718755454083481411 := by
  unfold tailWord_2034413
  simp only [CollatzResearch.WordTrace]
  refine ⟨74201137978676625923595893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49467425319117750615730595 74201137978676625923595893)
  ·
    refine ⟨6956356685500933680337115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74201137978676625923595893 6956356685500933680337115)
    ·
      refine ⟨10434535028251400520505673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6956356685500933680337115 10434535028251400520505673)
      ·
        refine ⟨7825901271188550390379255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10434535028251400520505673 7825901271188550390379255)
        ·
          refine ⟨11738851906782825585568883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825901271188550390379255 11738851906782825585568883)
          ·
            refine ⟨17608277860174238378353325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738851906782825585568883 17608277860174238378353325)
            ·
              refine ⟨6603104197565339391882497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17608277860174238378353325 6603104197565339391882497)
              ·
                refine ⟨4952328148174004543911873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6603104197565339391882497 4952328148174004543911873)
                ·
                  refine ⟨3714246111130503407933905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4952328148174004543911873 3714246111130503407933905)
                  ·
                    refine ⟨2785684583347877555950429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3714246111130503407933905 2785684583347877555950429)
                    ·
                      refine ⟨1044631718755454083481411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785684583347877555950429 1044631718755454083481411)
                      ·
                        rfl

theorem cell23_2034413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2034413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034413 prefixEnd_2034413 := by exact prefixLift 2034413
  have htrace : WordTrace (prefixWord ++ tailWord_2034413) baseStart_2034413 baseEnd_2034413 := by
    simpa [prefixWord, tailWord_2034413, baseEnd_2034413] using wordTrace_append hprefix tailTrace_2034413
  have hstable : (prefixWord ++ tailWord_2034413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034413).length < 2 ^ (prefixWord ++ tailWord_2034413).sum := by decide
  have hdescent : baseEnd_2034413 < baseStart_2034413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034503 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_2034503 : Nat := 118140960795 + 2034503 * 2 ^ 59
def prefixEnd_2034503 : Nat := 4983230072969 + 3 ^ 40 * 2034503 * 2
def baseEnd_2034503 : Nat := 1044677932014358731355997

theorem tailTrace_2034503 : CollatzResearch.WordTrace tailWord_2034503 prefixEnd_2034503 1044677932014358731355997 := by
  unfold tailWord_2034503
  simp only [CollatzResearch.WordTrace]
  refine ⟨74204420548350571294372163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49469613698900380862914775 74204420548350571294372163)
  ·
    refine ⟨111306630822525856941558245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74204420548350571294372163 111306630822525856941558245)
    ·
      refine ⟨20869993279223598176542171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111306630822525856941558245 20869993279223598176542171)
      ·
        refine ⟨31304989918835397264813257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20869993279223598176542171 31304989918835397264813257)
        ·
          refine ⟨23478742439126547948609943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31304989918835397264813257 23478742439126547948609943)
          ·
            refine ⟨35218113658689821922914915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23478742439126547948609943 35218113658689821922914915)
            ·
              refine ⟨52827170488034732884372373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35218113658689821922914915 52827170488034732884372373)
              ·
                refine ⟨2476273616626628103954955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52827170488034732884372373 2476273616626628103954955)
                ·
                  refine ⟨3714410424939942155932433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476273616626628103954955 3714410424939942155932433)
                  ·
                    refine ⟨2785807818704956616949325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3714410424939942155932433 2785807818704956616949325)
                    ·
                      refine ⟨1044677932014358731355997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2785807818704956616949325 1044677932014358731355997)
                      ·
                        rfl

theorem cell23_2034503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_2034503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034503 prefixEnd_2034503 := by exact prefixLift 2034503
  have htrace : WordTrace (prefixWord ++ tailWord_2034503) baseStart_2034503 baseEnd_2034503 := by
    simpa [prefixWord, tailWord_2034503, baseEnd_2034503] using wordTrace_append hprefix tailTrace_2034503
  have hstable : (prefixWord ++ tailWord_2034503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034503).length < 2 ^ (prefixWord ++ tailWord_2034503).sum := by decide
  have hdescent : baseEnd_2034503 < baseStart_2034503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034543 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 5, 3, 2]
def baseStart_2034543 : Nat := 118140960795 + 2034543 * 2 ^ 59
def prefixEnd_2034543 : Nat := 4983230072969 + 3 ^ 40 * 2034543 * 2
def baseEnd_2034543 : Nat := 1044698471240538574855813

theorem tailTrace_2034543 : CollatzResearch.WordTrace tailWord_2034543 prefixEnd_2034543 1044698471240538574855813 := by
  unfold tailWord_2034543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74205879468205658125828283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49470586312137105417218855 74205879468205658125828283)
  ·
    refine ⟨111308819202308487188742425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74205879468205658125828283 111308819202308487188742425)
    ·
      refine ⟨83481614401731365391556819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111308819202308487188742425 83481614401731365391556819)
      ·
        refine ⟨125222421602597048087335229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83481614401731365391556819 125222421602597048087335229)
        ·
          refine ⟨46958408100973893032750711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125222421602597048087335229 46958408100973893032750711)
          ·
            refine ⟨70437612151460839549126067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46958408100973893032750711 70437612151460839549126067)
            ·
              refine ⟨105656418227191259323689101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70437612151460839549126067 105656418227191259323689101)
              ·
                refine ⟨39621156835196722246383413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105656418227191259323689101 39621156835196722246383413)
                ·
                  refine ⟨3714483453299692710598445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39621156835196722246383413 3714483453299692710598445)
                  ·
                    refine ⟨1392931294987384766474417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714483453299692710598445 1392931294987384766474417)
                    ·
                      refine ⟨1044698471240538574855813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392931294987384766474417 1044698471240538574855813)
                      ·
                        rfl

theorem cell23_2034543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3, 2].length) (baseStart_2034543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034543 prefixEnd_2034543 := by exact prefixLift 2034543
  have htrace : WordTrace (prefixWord ++ tailWord_2034543) baseStart_2034543 baseEnd_2034543 := by
    simpa [prefixWord, tailWord_2034543, baseEnd_2034543] using wordTrace_append hprefix tailTrace_2034543
  have hstable : (prefixWord ++ tailWord_2034543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034543).length < 2 ^ (prefixWord ++ tailWord_2034543).sum := by decide
  have hdescent : baseEnd_2034543 < baseStart_2034543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034556 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_2034556 : Nat := 118140960795 + 2034556 * 2 ^ 59
def prefixEnd_2034556 : Nat := 4983230072969 + 3 ^ 40 * 2034556 * 2
def baseEnd_2034556 : Nat := 1044705146489047023993253

theorem tailTrace_2034556 : CollatzResearch.WordTrace tailWord_2034556 prefixEnd_2034556 1044705146489047023993253 := by
  unfold tailWord_2034556
  simp only [CollatzResearch.WordTrace]
  refine ⟨37103176808579280673025761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49470902411439040897367681 37103176808579280673025761)
  ·
    refine ⟨27827382606434460504769321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37103176808579280673025761 27827382606434460504769321)
    ·
      refine ⟨20870536954825845378576991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27827382606434460504769321 20870536954825845378576991)
      ·
        refine ⟨31305805432238768067865487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20870536954825845378576991 31305805432238768067865487)
        ·
          refine ⟨46958708148358152101798231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31305805432238768067865487 46958708148358152101798231)
          ·
            refine ⟨70438062222537228152697347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46958708148358152101798231 70438062222537228152697347)
            ·
              refine ⟨105657093333805842229046021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70438062222537228152697347 105657093333805842229046021)
              ·
                refine ⟨19810705000088595417946129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105657093333805842229046021 19810705000088595417946129)
                ·
                  refine ⟨14858028750066446563459597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19810705000088595417946129 14858028750066446563459597)
                  ·
                    refine ⟨5571760781274917461297349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14858028750066446563459597 5571760781274917461297349)
                    ·
                      refine ⟨1044705146489047023993253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5571760781274917461297349 1044705146489047023993253)
                      ·
                        rfl

theorem cell23_2034556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_2034556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034556 prefixEnd_2034556 := by exact prefixLift 2034556
  have htrace : WordTrace (prefixWord ++ tailWord_2034556) baseStart_2034556 baseEnd_2034556 := by
    simpa [prefixWord, tailWord_2034556, baseEnd_2034556] using wordTrace_append hprefix tailTrace_2034556
  have hstable : (prefixWord ++ tailWord_2034556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034556).length < 2 ^ (prefixWord ++ tailWord_2034556).sum := by decide
  have hdescent : baseEnd_2034556 < baseStart_2034556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034633 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 7, 2]
def baseStart_2034633 : Nat := 118140960795 + 2034633 * 2 ^ 59
def prefixEnd_2034633 : Nat := 4983230072969 + 3 ^ 40 * 2034633 * 2
def baseEnd_2034633 : Nat := 1044744684499443222730399

theorem tailTrace_2034633 : CollatzResearch.WordTrace tailWord_2034633 prefixEnd_2034633 1044744684499443222730399 := by
  unfold tailWord_2034633
  simp only [CollatzResearch.WordTrace]
  refine ⟨74209162037879603496604553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49472774691919735664403035 74209162037879603496604553)
  ·
    refine ⟨55656871528409702622453415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74209162037879603496604553 55656871528409702622453415)
    ·
      refine ⟨83485307292614553933680123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55656871528409702622453415 83485307292614553933680123)
      ·
        refine ⟨125227960938921830900520185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83485307292614553933680123 125227960938921830900520185)
        ·
          refine ⟨93920970704191373175390139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125227960938921830900520185 93920970704191373175390139)
          ·
            refine ⟨140881456056287059763085209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93920970704191373175390139 140881456056287059763085209)
            ·
              refine ⟨105661092042215294822313907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140881456056287059763085209 105661092042215294822313907)
              ·
                refine ⟨158491638063322942233470861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105661092042215294822313907 158491638063322942233470861)
                ·
                  refine ⟨59434364273746103337551573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158491638063322942233470861 59434364273746103337551573)
                  ·
                    refine ⟨1392992912665924296973865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59434364273746103337551573 1392992912665924296973865)
                    ·
                      refine ⟨1044744684499443222730399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1392992912665924296973865 1044744684499443222730399)
                      ·
                        rfl

theorem cell23_2034633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7, 2].length) (baseStart_2034633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034633 prefixEnd_2034633 := by exact prefixLift 2034633
  have htrace : WordTrace (prefixWord ++ tailWord_2034633) baseStart_2034633 baseEnd_2034633 := by
    simpa [prefixWord, tailWord_2034633, baseEnd_2034633] using wordTrace_append hprefix tailTrace_2034633
  have hstable : (prefixWord ++ tailWord_2034633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034633).length < 2 ^ (prefixWord ++ tailWord_2034633).sum := by decide
  have hdescent : baseEnd_2034633 < baseStart_2034633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034650 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_2034650 : Nat := 118140960795 + 2034650 * 2 ^ 59
def prefixEnd_2034650 : Nat := 4983230072969 + 3 ^ 40 * 2034650 * 2
def baseEnd_2034650 : Nat := 1044753413670569656217821

theorem tailTrace_2034650 : CollatzResearch.WordTrace tailWord_2034650 prefixEnd_2034650 1044753413670569656217821 := by
  unfold tailWord_2034650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552445519704503849993351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49473188052545343599982269 18552445519704503849993351)
  ·
    refine ⟨27828668279556755774990027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18552445519704503849993351 27828668279556755774990027)
    ·
      refine ⟨41743002419335133662485041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27828668279556755774990027 41743002419335133662485041)
      ·
        refine ⟨31307251814501350246863781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41743002419335133662485041 31307251814501350246863781)
        ·
          refine ⟨5870109715219003171286959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31307251814501350246863781 5870109715219003171286959)
          ·
            refine ⟨8805164572828504756930439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870109715219003171286959 8805164572828504756930439)
            ·
              refine ⟨13207746859242757135395659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805164572828504756930439 13207746859242757135395659)
              ·
                refine ⟨19811620288864135703093489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207746859242757135395659 19811620288864135703093489)
                ·
                  refine ⟨14858715216648101777320117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19811620288864135703093489 14858715216648101777320117)
                  ·
                    refine ⟨1393004551560759541623761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14858715216648101777320117 1393004551560759541623761)
                    ·
                      refine ⟨1044753413670569656217821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393004551560759541623761 1044753413670569656217821)
                      ·
                        rfl

theorem cell23_2034650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_2034650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034650 prefixEnd_2034650 := by exact prefixLift 2034650
  have htrace : WordTrace (prefixWord ++ tailWord_2034650) baseStart_2034650 baseEnd_2034650 := by
    simpa [prefixWord, tailWord_2034650, baseEnd_2034650] using wordTrace_append hprefix tailTrace_2034650
  have hstable : (prefixWord ++ tailWord_2034650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034650).length < 2 ^ (prefixWord ++ tailWord_2034650).sum := by decide
  have hdescent : baseEnd_2034650 < baseStart_2034650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034656 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_2034656 : Nat := 118140960795 + 2034656 * 2 ^ 59
def prefixEnd_2034656 : Nat := 4983230072969 + 3 ^ 40 * 2034656 * 2
def baseEnd_2034656 : Nat := 348252164851498877580931

theorem tailTrace_2034656 : CollatzResearch.WordTrace tailWord_2034656 prefixEnd_2034656 348252164851498877580931 := by
  unfold tailWord_2034656
  simp only [CollatzResearch.WordTrace]
  refine ⟨37105000458398139212345911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49473333944530852283127881 37105000458398139212345911)
  ·
    refine ⟨55657500687597208818518867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37105000458398139212345911 55657500687597208818518867)
    ·
      refine ⟨83486251031395813227778301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55657500687597208818518867 83486251031395813227778301)
      ·
        refine ⟨31307344136773429960416863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83486251031395813227778301 31307344136773429960416863)
        ·
          refine ⟨46961016205160144940625295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31307344136773429960416863 46961016205160144940625295)
          ·
            refine ⟨70441524307740217410937943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46961016205160144940625295 70441524307740217410937943)
            ·
              refine ⟨105662286461610326116406915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70441524307740217410937943 105662286461610326116406915)
              ·
                refine ⟨158493429692415489174610373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105662286461610326116406915 158493429692415489174610373)
                ·
                  refine ⟨29717518067327904220239445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158493429692415489174610373 29717518067327904220239445)
                  ·
                    refine ⟨348252164851498877580931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29717518067327904220239445 348252164851498877580931)
                    ·
                      rfl

theorem cell23_2034656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_2034656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034656 prefixEnd_2034656 := by exact prefixLift 2034656
  have htrace : WordTrace (prefixWord ++ tailWord_2034656) baseStart_2034656 baseEnd_2034656 := by
    simpa [prefixWord, tailWord_2034656, baseEnd_2034656] using wordTrace_append hprefix tailTrace_2034656
  have hstable : (prefixWord ++ tailWord_2034656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034656).length < 2 ^ (prefixWord ++ tailWord_2034656).sum := by decide
  have hdescent : baseEnd_2034656 < baseStart_2034656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034677 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2034677 : Nat := 118140960795 + 2034677 * 2 ^ 59
def prefixEnd_2034677 : Nat := 4983230072969 + 3 ^ 40 * 2034677 * 2
def baseEnd_2034677 : Nat := 348255759216080350193399

theorem tailTrace_2034677 : CollatzResearch.WordTrace tailWord_2034677 prefixEnd_2034677 348255759216080350193399 := by
  unfold tailWord_2034677
  simp only [CollatzResearch.WordTrace]
  refine ⟨74210766849720199011206285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49473844566480132674137523 74210766849720199011206285)
  ·
    refine ⟨27829037568645074629202357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74210766849720199011206285 27829037568645074629202357)
    ·
      refine ⟨2608972272060475746487721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27829037568645074629202357 2608972272060475746487721)
      ·
        refine ⟨1956729204045356809865791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2608972272060475746487721 1956729204045356809865791)
        ·
          refine ⟨2935093806068035214798687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956729204045356809865791 2935093806068035214798687)
          ·
            refine ⟨4402640709102052822198031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935093806068035214798687 4402640709102052822198031)
            ·
              refine ⟨6603961063653079233297047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402640709102052822198031 6603961063653079233297047)
              ·
                refine ⟨9905941595479618849945571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603961063653079233297047 9905941595479618849945571)
                ·
                  refine ⟨14858912393219428274918357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9905941595479618849945571 14858912393219428274918357)
                  ·
                    refine ⟨348255759216080350193399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14858912393219428274918357 348255759216080350193399)
                    ·
                      rfl

theorem cell23_2034677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2034677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034677 prefixEnd_2034677 := by exact prefixLift 2034677
  have htrace : WordTrace (prefixWord ++ tailWord_2034677) baseStart_2034677 baseEnd_2034677 := by
    simpa [prefixWord, tailWord_2034677, baseEnd_2034677] using wordTrace_append hprefix tailTrace_2034677
  have hstable : (prefixWord ++ tailWord_2034677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034677).length < 2 ^ (prefixWord ++ tailWord_2034677).sum := by decide
  have hdescent : baseEnd_2034677 < baseStart_2034677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034758 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2034758 : Nat := 118140960795 + 2034758 * 2 ^ 59
def prefixEnd_2034758 : Nat := 4983230072969 + 3 ^ 40 * 2034758 * 2
def baseEnd_2034758 : Nat := 348269623193751744555775

theorem tailTrace_2034758 : CollatzResearch.WordTrace tailWord_2034758 prefixEnd_2034758 348269623193751744555775 := by
  unfold tailWord_2034758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319178786325835932653279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49475814108284499896603285 2319178786325835932653279)
  ·
    refine ⟨3478768179488753898979919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319178786325835932653279 3478768179488753898979919)
    ·
      refine ⟨5218152269233130848469879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478768179488753898979919 5218152269233130848469879)
      ·
        refine ⟨7827228403849696272704819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218152269233130848469879 7827228403849696272704819)
        ·
          refine ⟨11740842605774544409057229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827228403849696272704819 11740842605774544409057229)
          ·
            refine ⟨4402815977165454153396461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11740842605774544409057229 4402815977165454153396461)
            ·
              refine ⟨1651055991437045307523673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4402815977165454153396461 1651055991437045307523673)
              ·
                refine ⟨1238291993577783980642755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651055991437045307523673 1238291993577783980642755)
                ·
                  refine ⟨1857437990366675970964133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238291993577783980642755 1857437990366675970964133)
                  ·
                    refine ⟨348269623193751744555775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857437990366675970964133 348269623193751744555775)
                    ·
                      rfl

theorem cell23_2034758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2034758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034758 prefixEnd_2034758 := by exact prefixLift 2034758
  have htrace : WordTrace (prefixWord ++ tailWord_2034758) baseStart_2034758 baseEnd_2034758 := by
    simpa [prefixWord, tailWord_2034758, baseEnd_2034758] using wordTrace_append hprefix tailTrace_2034758
  have hstable : (prefixWord ++ tailWord_2034758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034758).length < 2 ^ (prefixWord ++ tailWord_2034758).sum := by decide
  have hdescent : baseEnd_2034758 < baseStart_2034758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034780 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2034780 : Nat := 118140960795 + 2034780 * 2 ^ 59
def prefixEnd_2034780 : Nat := 4983230072969 + 3 ^ 40 * 2034780 * 2
def baseEnd_2034780 : Nat := 348273388718551382530741

theorem tailTrace_2034780 : CollatzResearch.WordTrace tailWord_2034780 prefixEnd_2034780 348273388718551382530741 := by
  unfold tailWord_2034780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107261784173523801102897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49476349045564698401470529 37107261784173523801102897)
  ·
    refine ⟨27830446338130142850827173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37107261784173523801102897 27830446338130142850827173)
    ·
      refine ⟨5218208688399401784530095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27830446338130142850827173 5218208688399401784530095)
      ·
        refine ⟨7827313032599102676795143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218208688399401784530095 7827313032599102676795143)
        ·
          refine ⟨11740969548898654015192715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827313032599102676795143 11740969548898654015192715)
          ·
            refine ⟨17611454323347981022789073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740969548898654015192715 17611454323347981022789073)
            ·
              refine ⟨13208590742510985767091805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17611454323347981022789073 13208590742510985767091805)
              ·
                refine ⟨4953221528441619662659427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13208590742510985767091805 4953221528441619662659427)
                ·
                  refine ⟨7429832292662429493989141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953221528441619662659427 7429832292662429493989141)
                  ·
                    refine ⟨348273388718551382530741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7429832292662429493989141 348273388718551382530741)
                    ·
                      rfl

theorem cell23_2034780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2034780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034780 prefixEnd_2034780 := by exact prefixLift 2034780
  have htrace : WordTrace (prefixWord ++ tailWord_2034780) baseStart_2034780 baseEnd_2034780 := by
    simpa [prefixWord, tailWord_2034780, baseEnd_2034780] using wordTrace_append hprefix tailTrace_2034780
  have hstable : (prefixWord ++ tailWord_2034780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034780).length < 2 ^ (prefixWord ++ tailWord_2034780).sum := by decide
  have hdescent : baseEnd_2034780 < baseStart_2034780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034783 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_2034783 : Nat := 118140960795 + 2034783 * 2 ^ 59
def prefixEnd_2034783 : Nat := 4983230072969 + 3 ^ 40 * 2034783 * 2
def baseEnd_2034783 : Nat := 1044821706597617635854709

theorem tailTrace_2034783 : CollatzResearch.WordTrace tailWord_2034783 prefixEnd_2034783 1044821706597617635854709 := by
  unfold tailWord_2034783
  simp only [CollatzResearch.WordTrace]
  refine ⟨74214632987336179114565003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49476421991557452743043335 74214632987336179114565003)
  ·
    refine ⟨111321949481004268671847505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74214632987336179114565003 111321949481004268671847505)
    ·
      refine ⟨83491462110753201503885629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111321949481004268671847505 83491462110753201503885629)
      ·
        refine ⟨31309298291532450563957111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83491462110753201503885629 31309298291532450563957111)
        ·
          refine ⟨46963947437298675845935667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31309298291532450563957111 46963947437298675845935667)
          ·
            refine ⟨70445921155948013768903501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46963947437298675845935667 70445921155948013768903501)
            ·
              refine ⟨26417220433480505163338813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70445921155948013768903501 26417220433480505163338813)
              ·
                refine ⟨9906457662555189436252055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26417220433480505163338813 9906457662555189436252055)
                ·
                  refine ⟨14859686493832784154378083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9906457662555189436252055 14859686493832784154378083)
                  ·
                    refine ⟨22289529740749176231567125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14859686493832784154378083 22289529740749176231567125)
                    ·
                      refine ⟨1044821706597617635854709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22289529740749176231567125 1044821706597617635854709)
                      ·
                        rfl

theorem cell23_2034783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_2034783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034783 prefixEnd_2034783 := by exact prefixLift 2034783
  have htrace : WordTrace (prefixWord ++ tailWord_2034783) baseStart_2034783 baseEnd_2034783 := by
    simpa [prefixWord, tailWord_2034783, baseEnd_2034783] using wordTrace_append hprefix tailTrace_2034783
  have hstable : (prefixWord ++ tailWord_2034783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034783).length < 2 ^ (prefixWord ++ tailWord_2034783).sum := by decide
  have hdescent : baseEnd_2034783 < baseStart_2034783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034787 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 5, 2, 2]
def baseStart_2034787 : Nat := 118140960795 + 2034787 * 2 ^ 59
def prefixEnd_2034787 : Nat := 4983230072969 + 3 ^ 40 * 2034787 * 2
def baseEnd_2034787 : Nat := 1044823760520235620204691

theorem tailTrace_2034787 : CollatzResearch.WordTrace tailWord_2034787 prefixEnd_2034787 1044823760520235620204691 := by
  unfold tailWord_2034787
  simp only [CollatzResearch.WordTrace]
  refine ⟨74214778879321687797710615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49476519252881125198473743 74214778879321687797710615)
  ·
    refine ⟨111322168318982531696565923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74214778879321687797710615 111322168318982531696565923)
    ·
      refine ⟨166983252478473797544848885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111322168318982531696565923 166983252478473797544848885)
      ·
        refine ⟨15654679919856918519829583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166983252478473797544848885 15654679919856918519829583)
        ·
          refine ⟨23482019879785377779744375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15654679919856918519829583 23482019879785377779744375)
          ·
            refine ⟨35223029819678066669616563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23482019879785377779744375 35223029819678066669616563)
            ·
              refine ⟨52834544729517100004424845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35223029819678066669616563 52834544729517100004424845)
              ·
                refine ⟨19812954273568912501659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52834544729517100004424845 19812954273568912501659317)
                ·
                  refine ⟨1857464463147085547030561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19812954273568912501659317 1857464463147085547030561)
                  ·
                    refine ⟨1393098347360314160272921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1857464463147085547030561 1393098347360314160272921)
                    ·
                      refine ⟨1044823760520235620204691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393098347360314160272921 1044823760520235620204691)
                      ·
                        rfl

theorem cell23_2034787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_2034787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034787 prefixEnd_2034787 := by exact prefixLift 2034787
  have htrace : WordTrace (prefixWord ++ tailWord_2034787) baseStart_2034787 baseEnd_2034787 := by
    simpa [prefixWord, tailWord_2034787, baseEnd_2034787] using wordTrace_append hprefix tailTrace_2034787
  have hstable : (prefixWord ++ tailWord_2034787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034787).length < 2 ^ (prefixWord ++ tailWord_2034787).sum := by decide
  have hdescent : baseEnd_2034787 < baseStart_2034787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034793 : List Nat := [1, 2, 1, 1, 1, 6, 2, 9]
def baseStart_2034793 : Nat := 118140960795 + 2034793 * 2 ^ 59
def prefixEnd_2034793 : Nat := 4983230072969 + 3 ^ 40 * 2034793 * 2
def baseEnd_2034793 : Nat := 38697290422376392471469

theorem tailTrace_2034793 : CollatzResearch.WordTrace tailWord_2034793 prefixEnd_2034793 38697290422376392471469 := by
  unfold tailWord_2034793
  simp only [CollatzResearch.WordTrace]
  refine ⟨74214997717299950822429033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49476665144866633881619355 74214997717299950822429033)
  ·
    refine ⟨55661248287974963116821775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74214997717299950822429033 55661248287974963116821775)
    ·
      refine ⟨83491872431962444675232663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55661248287974963116821775 83491872431962444675232663)
      ·
        refine ⟨125237808647943667012848995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83491872431962444675232663 125237808647943667012848995)
        ·
          refine ⟨187856712971915500519273493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125237808647943667012848995 187856712971915500519273493)
          ·
            refine ⟨8805783420558539086840945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187856712971915500519273493 8805783420558539086840945)
            ·
              refine ⟨6604337565418904315130709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8805783420558539086840945 6604337565418904315130709)
              ·
                refine ⟨38697290422376392471469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6604337565418904315130709 38697290422376392471469)
                ·
                  rfl

theorem cell23_2034793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 9].length) (baseStart_2034793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034793 prefixEnd_2034793 := by exact prefixLift 2034793
  have htrace : WordTrace (prefixWord ++ tailWord_2034793) baseStart_2034793 baseEnd_2034793 := by
    simpa [prefixWord, tailWord_2034793, baseEnd_2034793] using wordTrace_append hprefix tailTrace_2034793
  have hstable : (prefixWord ++ tailWord_2034793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034793).length < 2 ^ (prefixWord ++ tailWord_2034793).sum := by decide
  have hdescent : baseEnd_2034793 < baseStart_2034793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034800 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_2034800 : Nat := 118140960795 + 2034800 * 2 ^ 59
def prefixEnd_2034800 : Nat := 4983230072969 + 3 ^ 40 * 2034800 * 2
def baseEnd_2034800 : Nat := 1044830435768744069342131

theorem tailTrace_2034800 : CollatzResearch.WordTrace tailWord_2034800 prefixEnd_2034800 1044830435768744069342131 := by
  unfold tailWord_2034800
  simp only [CollatzResearch.WordTrace]
  refine ⟨37107626514137295508966927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49476835352183060678622569 37107626514137295508966927)
  ·
    refine ⟨55661439771205943263450391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37107626514137295508966927 55661439771205943263450391)
    ·
      refine ⟨83492159656808914895175587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55661439771205943263450391 83492159656808914895175587)
      ·
        refine ⟨125238239485213372342763381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83492159656808914895175587 125238239485213372342763381)
        ·
          refine ⟨11741084951738753657134067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125238239485213372342763381 11741084951738753657134067)
          ·
            refine ⟨17611627427608130485701101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741084951738753657134067 17611627427608130485701101)
            ·
              refine ⟨6604360285353048932137913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17611627427608130485701101 6604360285353048932137913)
              ·
                refine ⟨4953270214014786699103435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604360285353048932137913 4953270214014786699103435)
                ·
                  refine ⟨7429905321022180048655153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953270214014786699103435 7429905321022180048655153)
                  ·
                    refine ⟨5572428990766635036491365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7429905321022180048655153 5572428990766635036491365)
                    ·
                      refine ⟨1044830435768744069342131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5572428990766635036491365 1044830435768744069342131)
                      ·
                        rfl

theorem cell23_2034800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_2034800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034800 prefixEnd_2034800 := by exact prefixLift 2034800
  have htrace : WordTrace (prefixWord ++ tailWord_2034800) baseStart_2034800 baseEnd_2034800 := by
    simpa [prefixWord, tailWord_2034800, baseEnd_2034800] using wordTrace_append hprefix tailTrace_2034800
  have hstable : (prefixWord ++ tailWord_2034800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034800).length < 2 ^ (prefixWord ++ tailWord_2034800).sum := by decide
  have hdescent : baseEnd_2034800 < baseStart_2034800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034858 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2034858 : Nat := 118140960795 + 2034858 * 2 ^ 59
def prefixEnd_2034858 : Nat := 4983230072969 + 3 ^ 40 * 2034858 * 2
def baseEnd_2034858 : Nat := 1044860217646704842416865

theorem tailTrace_2034858 : CollatzResearch.WordTrace tailWord_2034858 prefixEnd_2034858 1044860217646704842416865 := by
  unfold tailWord_2034858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18554342115516116730886307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49478245641376311282363485 18554342115516116730886307)
  ·
    refine ⟨27831513173274175096329461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18554342115516116730886307 27831513173274175096329461)
    ·
      refine ⟨2609204359994453915280887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27831513173274175096329461 2609204359994453915280887)
      ·
        refine ⟨3913806539991680872921331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609204359994453915280887 3913806539991680872921331)
        ·
          refine ⟨5870709809987521309381997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913806539991680872921331 5870709809987521309381997)
          ·
            refine ⟨2201516178745320491018249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5870709809987521309381997 2201516178745320491018249)
            ·
              refine ⟨1651137134058990368263687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2201516178745320491018249 1651137134058990368263687)
              ·
                refine ⟨2476705701088485552395531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651137134058990368263687 2476705701088485552395531)
                ·
                  refine ⟨3715058551632728328593297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476705701088485552395531 3715058551632728328593297)
                  ·
                    refine ⟨2786293913724546246444973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3715058551632728328593297 2786293913724546246444973)
                    ·
                      refine ⟨1044860217646704842416865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2786293913724546246444973 1044860217646704842416865)
                      ·
                        rfl

theorem cell23_2034858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2034858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034858 prefixEnd_2034858 := by exact prefixLift 2034858
  have htrace : WordTrace (prefixWord ++ tailWord_2034858) baseStart_2034858 baseEnd_2034858 := by
    simpa [prefixWord, tailWord_2034858, baseEnd_2034858] using wordTrace_append hprefix tailTrace_2034858
  have hstable : (prefixWord ++ tailWord_2034858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034858).length < 2 ^ (prefixWord ++ tailWord_2034858).sum := by decide
  have hdescent : baseEnd_2034858 < baseStart_2034858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034877 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_2034877 : Nat := 118140960795 + 2034877 * 2 ^ 59
def prefixEnd_2034877 : Nat := 4983230072969 + 3 ^ 40 * 2034877 * 2
def baseEnd_2034877 : Nat := 1044869973779140268079277

theorem tailTrace_2034877 : CollatzResearch.WordTrace tailWord_2034877 prefixEnd_2034877 1044869973779140268079277 := by
  unfold tailWord_2034877
  simp only [CollatzResearch.WordTrace]
  refine ⟨74218061448995633168486885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49478707632663755445657923 74218061448995633168486885)
  ·
    refine ⟨13915886521686681219091291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74218061448995633168486885 13915886521686681219091291)
    ·
      refine ⟨20873829782530021828636937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13915886521686681219091291 20873829782530021828636937)
      ·
        refine ⟨15655372336897516371477703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20873829782530021828636937 15655372336897516371477703)
        ·
          refine ⟨23483058505346274557216555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15655372336897516371477703 23483058505346274557216555)
          ·
            refine ⟨35224587758019411835824833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483058505346274557216555 35224587758019411835824833)
            ·
              refine ⟨26418440818514558876868625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35224587758019411835824833 26418440818514558876868625)
              ·
                refine ⟨19813830613885919157651469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26418440818514558876868625 19813830613885919157651469)
                ·
                  refine ⟨7430186480207219684119301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19813830613885919157651469 7430186480207219684119301)
                  ·
                    refine ⟨1393159965038853690772369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7430186480207219684119301 1393159965038853690772369)
                    ·
                      refine ⟨1044869973779140268079277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393159965038853690772369 1044869973779140268079277)
                      ·
                        rfl

theorem cell23_2034877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_2034877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034877 prefixEnd_2034877 := by exact prefixLift 2034877
  have htrace : WordTrace (prefixWord ++ tailWord_2034877) baseStart_2034877 baseEnd_2034877 := by
    simpa [prefixWord, tailWord_2034877, baseEnd_2034877] using wordTrace_append hprefix tailTrace_2034877
  have hstable : (prefixWord ++ tailWord_2034877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034877).length < 2 ^ (prefixWord ++ tailWord_2034877).sum := by decide
  have hdescent : baseEnd_2034877 < baseStart_2034877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034937 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 5, 2]
def baseStart_2034937 : Nat := 118140960795 + 2034937 * 2 ^ 59
def prefixEnd_2034937 : Nat := 4983230072969 + 3 ^ 40 * 2034937 * 2
def baseEnd_2034937 : Nat := 1044900782618410033329001

theorem tailTrace_2034937 : CollatzResearch.WordTrace tailWord_2034937 prefixEnd_2034937 1044900782618410033329001 := by
  unfold tailWord_2034937
  simp only [CollatzResearch.WordTrace]
  refine ⟨74220249828778263415671065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49480166552518842277114043 74220249828778263415671065)
  ·
    refine ⟨55665187371583697561753299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74220249828778263415671065 55665187371583697561753299)
    ·
      refine ⟨83497781057375546342629949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55665187371583697561753299 83497781057375546342629949)
      ·
        refine ⟨31311667896515829878486231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83497781057375546342629949 31311667896515829878486231)
        ·
          refine ⟨46967501844773744817729347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31311667896515829878486231 46967501844773744817729347)
          ·
            refine ⟨70451252767160617226594021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46967501844773744817729347 70451252767160617226594021)
            ·
              refine ⟨13209609893842615729986379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70451252767160617226594021 13209609893842615729986379)
              ·
                refine ⟨19814414840763923594979569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13209609893842615729986379 19814414840763923594979569)
                ·
                  refine ⟨14860811130572942696234677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19814414840763923594979569 14860811130572942696234677)
                  ·
                    refine ⟨1393201043491213377772001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14860811130572942696234677 1393201043491213377772001)
                    ·
                      refine ⟨1044900782618410033329001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393201043491213377772001 1044900782618410033329001)
                      ·
                        rfl

theorem cell23_2034937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_2034937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034937 prefixEnd_2034937 := by exact prefixLift 2034937
  have htrace : WordTrace (prefixWord ++ tailWord_2034937) baseStart_2034937 baseEnd_2034937 := by
    simpa [prefixWord, tailWord_2034937, baseEnd_2034937] using wordTrace_append hprefix tailTrace_2034937
  have hstable : (prefixWord ++ tailWord_2034937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034937).length < 2 ^ (prefixWord ++ tailWord_2034937).sum := by decide
  have hdescent : baseEnd_2034937 < baseStart_2034937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2034984 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2034984 : Nat := 118140960795 + 2034984 * 2 ^ 59
def prefixEnd_2034984 : Nat := 4983230072969 + 3 ^ 40 * 2034984 * 2
def baseEnd_2034984 : Nat := 1044924916209171349441285

theorem tailTrace_2034984 : CollatzResearch.WordTrace tailWord_2034984 prefixEnd_2034984 1044924916209171349441285 := by
  unfold tailWord_2034984
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110982029803995221316003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49481309373071993628421337 37110982029803995221316003)
  ·
    refine ⟨55666473044705992831974005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37110982029803995221316003 55666473044705992831974005)
    ·
      refine ⟨5218731847941186827997563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55666473044705992831974005 5218731847941186827997563)
      ·
        refine ⟨7828097771911780241996345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218731847941186827997563 7828097771911780241996345)
        ·
          refine ⟨5871073328933835181497259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7828097771911780241996345 5871073328933835181497259)
          ·
            refine ⟨8806609993400752772245889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871073328933835181497259 8806609993400752772245889)
            ·
              refine ⟨6604957495050564579184417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806609993400752772245889 6604957495050564579184417)
              ·
                refine ⟨4953718121287923434388313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604957495050564579184417 4953718121287923434388313)
                ·
                  refine ⟨3715288590965942575791235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953718121287923434388313 3715288590965942575791235)
                  ·
                    refine ⟨5572932886448913863686853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715288590965942575791235 5572932886448913863686853)
                    ·
                      refine ⟨1044924916209171349441285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5572932886448913863686853 1044924916209171349441285)
                      ·
                        rfl

theorem cell23_2034984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2034984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2034984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2034984 prefixEnd_2034984 := by exact prefixLift 2034984
  have htrace : WordTrace (prefixWord ++ tailWord_2034984) baseStart_2034984 baseEnd_2034984 := by
    simpa [prefixWord, tailWord_2034984, baseEnd_2034984] using wordTrace_append hprefix tailTrace_2034984
  have hstable : (prefixWord ++ tailWord_2034984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2034984).length < 2 ^ (prefixWord ++ tailWord_2034984).sum := by decide
  have hdescent : baseEnd_2034984 < baseStart_2034984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2034984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035001 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2035001 : Nat := 118140960795 + 2035001 * 2 ^ 59
def prefixEnd_2035001 : Nat := 4983230072969 + 3 ^ 40 * 2035001 * 2
def baseEnd_2035001 : Nat := 1044933645380297782928707

theorem tailTrace_2035001 : CollatzResearch.WordTrace tailWord_2035001 prefixEnd_2035001 1044933645380297782928707 := by
  unfold tailWord_2035001
  simp only [CollatzResearch.WordTrace]
  refine ⟨74222584100546402346000857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49481722733697601564000571 74222584100546402346000857)
  ·
    refine ⟨55666938075409801759500643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74222584100546402346000857 55666938075409801759500643)
    ·
      refine ⟨83500407113114702639250965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55666938075409801759500643 83500407113114702639250965)
      ·
        refine ⟨3914081583427251686214889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83500407113114702639250965 3914081583427251686214889)
        ·
          refine ⟨2935561187570438764661167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3914081583427251686214889 2935561187570438764661167)
          ·
            refine ⟨4403341781355658146991751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935561187570438764661167 4403341781355658146991751)
            ·
              refine ⟨6605012672033487220487627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403341781355658146991751 6605012672033487220487627)
              ·
                refine ⟨9907519008050230830731441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605012672033487220487627 9907519008050230830731441)
                ·
                  refine ⟨7430639256037673123048581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9907519008050230830731441 7430639256037673123048581)
                  ·
                    refine ⟨1393244860507063710571609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7430639256037673123048581 1393244860507063710571609)
                    ·
                      refine ⟨1044933645380297782928707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393244860507063710571609 1044933645380297782928707)
                      ·
                        rfl

theorem cell23_2035001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2035001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035001 prefixEnd_2035001 := by exact prefixLift 2035001
  have htrace : WordTrace (prefixWord ++ tailWord_2035001) baseStart_2035001 baseEnd_2035001 := by
    simpa [prefixWord, tailWord_2035001, baseEnd_2035001] using wordTrace_append hprefix tailTrace_2035001
  have hstable : (prefixWord ++ tailWord_2035001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035001).length < 2 ^ (prefixWord ++ tailWord_2035001).sum := by decide
  have hdescent : baseEnd_2035001 < baseStart_2035001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035007 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 6]
def baseStart_2035007 : Nat := 118140960795 + 2035007 * 2 ^ 59
def prefixEnd_2035007 : Nat := 4983230072969 + 3 ^ 40 * 2035007 * 2
def baseEnd_2035007 : Nat := 116104080696024973272631

theorem tailTrace_2035007 : CollatzResearch.WordTrace tailWord_2035007 prefixEnd_2035007 116104080696024973272631 := by
  unfold tailWord_2035007
  simp only [CollatzResearch.WordTrace]
  refine ⟨74222802938524665370719275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49481868625683110247146183 74222802938524665370719275)
  ·
    refine ⟨111334204407786998056078913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74222802938524665370719275 111334204407786998056078913)
    ·
      refine ⟨83500653305840248542059185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111334204407786998056078913 83500653305840248542059185)
      ·
        refine ⟨62625489979380186406544389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83500653305840248542059185 62625489979380186406544389)
        ·
          refine ⟨11742279371133784951227073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62625489979380186406544389 11742279371133784951227073)
          ·
            refine ⟨8806709528350338713420305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11742279371133784951227073 8806709528350338713420305)
            ·
              refine ⟨6605032146262754035065229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806709528350338713420305 6605032146262754035065229)
              ·
                refine ⟨2476887054848532763149461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6605032146262754035065229 2476887054848532763149461)
                ·
                  refine ⟨116104080696024973272631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2476887054848532763149461 116104080696024973272631)
                  ·
                    rfl

theorem cell23_2035007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 6].length) (baseStart_2035007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035007 prefixEnd_2035007 := by exact prefixLift 2035007
  have htrace : WordTrace (prefixWord ++ tailWord_2035007) baseStart_2035007 baseEnd_2035007 := by
    simpa [prefixWord, tailWord_2035007, baseEnd_2035007] using wordTrace_append hprefix tailTrace_2035007
  have hstable : (prefixWord ++ tailWord_2035007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035007).length < 2 ^ (prefixWord ++ tailWord_2035007).sum := by decide
  have hdescent : baseEnd_2035007 < baseStart_2035007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035057 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_2035057 : Nat := 118140960795 + 2035057 * 2 ^ 59
def prefixEnd_2035057 : Nat := 4983230072969 + 3 ^ 40 * 2035057 * 2
def baseEnd_2035057 : Nat := 1044962400296949563828449

theorem tailTrace_2035057 : CollatzResearch.WordTrace tailWord_2035057 prefixEnd_2035057 1044962400296949563828449 := by
  unfold tailWord_2035057
  simp only [CollatzResearch.WordTrace]
  refine ⟨74224626588343523910039425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49483084392229015940026283 74224626588343523910039425)
  ·
    refine ⟨55668469941257642932529569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74224626588343523910039425 55668469941257642932529569)
    ·
      refine ⟨41751352455943232199397177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55668469941257642932529569 41751352455943232199397177)
      ·
        refine ⟨31313514341957424149547883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41751352455943232199397177 31313514341957424149547883)
        ·
          refine ⟨46970271512936136224321825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31313514341957424149547883 46970271512936136224321825)
          ·
            refine ⟨35227703634702102168241369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46970271512936136224321825 35227703634702102168241369)
            ·
              refine ⟨26420777726026576626181027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35227703634702102168241369 26420777726026576626181027)
              ·
                refine ⟨39631166589039864939271541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26420777726026576626181027 39631166589039864939271541)
                ·
                  refine ⟨3715421867722487338056707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39631166589039864939271541 3715421867722487338056707)
                  ·
                    refine ⟨5573132801583731007085061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3715421867722487338056707 5573132801583731007085061)
                    ·
                      refine ⟨1044962400296949563828449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5573132801583731007085061 1044962400296949563828449)
                      ·
                        rfl

theorem cell23_2035057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_2035057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035057 prefixEnd_2035057 := by exact prefixLift 2035057
  have htrace : WordTrace (prefixWord ++ tailWord_2035057) baseStart_2035057 baseEnd_2035057 := by
    simpa [prefixWord, tailWord_2035057, baseEnd_2035057] using wordTrace_append hprefix tailTrace_2035057
  have hstable : (prefixWord ++ tailWord_2035057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035057).length < 2 ^ (prefixWord ++ tailWord_2035057).sum := by decide
  have hdescent : baseEnd_2035057 < baseStart_2035057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035097 : List Nat := [1, 2, 1, 2, 1, 7, 9]
def baseStart_2035097 : Nat := 118140960795 + 2035097 * 2 ^ 59
def prefixEnd_2035097 : Nat := 4983230072969 + 3 ^ 40 * 2035097 * 2
def baseEnd_2035097 : Nat := 12901023944729992683065

theorem tailTrace_2035097 : CollatzResearch.WordTrace tailWord_2035097 prefixEnd_2035097 12901023944729992683065 := by
  unfold tailWord_2035097
  simp only [CollatzResearch.WordTrace]
  refine ⟨74226085508198610741495545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49484057005465740494330363 74226085508198610741495545)
  ·
    refine ⟨55669564131148958056121659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74226085508198610741495545 55669564131148958056121659)
    ·
      refine ⟨83504346196723437084182489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55669564131148958056121659 83504346196723437084182489)
      ·
        refine ⟨62628259647542577813136867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83504346196723437084182489 62628259647542577813136867)
        ·
          refine ⟨93942389471313866719705301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62628259647542577813136867 93942389471313866719705301)
          ·
            refine ⟨2201774753233918751243093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93942389471313866719705301 2201774753233918751243093)
            ·
              refine ⟨12901023944729992683065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2201774753233918751243093 12901023944729992683065)
              ·
                rfl

theorem cell23_2035097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 9].length) (baseStart_2035097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035097 prefixEnd_2035097 := by exact prefixLift 2035097
  have htrace : WordTrace (prefixWord ++ tailWord_2035097) baseStart_2035097 baseEnd_2035097 := by
    simpa [prefixWord, tailWord_2035097, baseEnd_2035097] using wordTrace_append hprefix tailTrace_2035097
  have hstable : (prefixWord ++ tailWord_2035097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035097).length < 2 ^ (prefixWord ++ tailWord_2035097).sum := by decide
  have hdescent : baseEnd_2035097 < baseStart_2035097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035102 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2035102 : Nat := 118140960795 + 2035102 * 2 ^ 59
def prefixEnd_2035102 : Nat := 4983230072969 + 3 ^ 40 * 2035102 * 2
def baseEnd_2035102 : Nat := 1044985506926401887765743

theorem tailTrace_2035102 : CollatzResearch.WordTrace tailWord_2035102 prefixEnd_2035102 1044985506926401887765743 := by
  unfold tailWord_2035102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9278283484147562074428445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49484178582120331063618373 9278283484147562074428445)
  ·
    refine ⟨3479356306555335777910667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9278283484147562074428445 3479356306555335777910667)
    ·
      refine ⟨5219034459833003666866001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479356306555335777910667 5219034459833003666866001)
      ·
        refine ⟨3914275844874752750149501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5219034459833003666866001 3914275844874752750149501)
        ·
          refine ⟨1467853441828032281306063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3914275844874752750149501 1467853441828032281306063)
          ·
            refine ⟨2201780162742048421959095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467853441828032281306063 2201780162742048421959095)
            ·
              refine ⟨3302670244113072632938643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2201780162742048421959095 3302670244113072632938643)
              ·
                refine ⟨4954005366169608949407965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302670244113072632938643 4954005366169608949407965)
                ·
                  refine ⟨1857752012313603356027987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4954005366169608949407965 1857752012313603356027987)
                  ·
                    refine ⟨2786628018470405034041981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1857752012313603356027987 2786628018470405034041981)
                    ·
                      refine ⟨1044985506926401887765743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2786628018470405034041981 1044985506926401887765743)
                      ·
                        rfl

theorem cell23_2035102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2035102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035102 prefixEnd_2035102 := by exact prefixLift 2035102
  have htrace : WordTrace (prefixWord ++ tailWord_2035102) baseStart_2035102 baseEnd_2035102 := by
    simpa [prefixWord, tailWord_2035102, baseEnd_2035102] using wordTrace_append hprefix tailTrace_2035102
  have hstable : (prefixWord ++ tailWord_2035102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035102).length < 2 ^ (prefixWord ++ tailWord_2035102).sum := by decide
  have hdescent : baseEnd_2035102 < baseStart_2035102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035151 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 1, 3, 2]
def baseStart_2035151 : Nat := 118140960795 + 2035151 * 2 ^ 59
def prefixEnd_2035151 : Nat := 4983230072969 + 3 ^ 40 * 2035151 * 2
def baseEnd_2035151 : Nat := 1045010667478472196053017

theorem tailTrace_2035151 : CollatzResearch.WordTrace tailWord_2035151 prefixEnd_2035151 1045010667478472196053017 := by
  unfold tailWord_2035151
  simp only [CollatzResearch.WordTrace]
  refine ⟨74228055050002977963961307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49485370033335318642640871 74228055050002977963961307)
  ·
    refine ⟨111342082575004466945941961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74228055050002977963961307 111342082575004466945941961)
    ·
      refine ⟨83506561931253350209456471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111342082575004466945941961 83506561931253350209456471)
      ·
        refine ⟨125259842896880025314184707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83506561931253350209456471 125259842896880025314184707)
        ·
          refine ⟨187889764345320037971277061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125259842896880025314184707 187889764345320037971277061)
          ·
            refine ⟨35229330814747507119614449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187889764345320037971277061 35229330814747507119614449)
            ·
              refine ⟨26421998111060630339710837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35229330814747507119614449 26421998111060630339710837)
              ·
                refine ⟨2477062322911934094347891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26421998111060630339710837 2477062322911934094347891)
                ·
                  refine ⟨3715593484367901141521837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477062322911934094347891 3715593484367901141521837)
                  ·
                    refine ⟨1393347556637962928070689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715593484367901141521837 1393347556637962928070689)
                    ·
                      refine ⟨1045010667478472196053017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393347556637962928070689 1045010667478472196053017)
                      ·
                        rfl

theorem cell23_2035151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3, 2].length) (baseStart_2035151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035151 prefixEnd_2035151 := by exact prefixLift 2035151
  have htrace : WordTrace (prefixWord ++ tailWord_2035151) baseStart_2035151 baseEnd_2035151 := by
    simpa [prefixWord, tailWord_2035151, baseEnd_2035151] using wordTrace_append hprefix tailTrace_2035151
  have hstable : (prefixWord ++ tailWord_2035151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035151).length < 2 ^ (prefixWord ++ tailWord_2035151).sum := by decide
  have hdescent : baseEnd_2035151 < baseStart_2035151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
