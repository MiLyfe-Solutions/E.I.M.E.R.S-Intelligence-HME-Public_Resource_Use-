import V185TrunkScan23Chunk1186

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7032931 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 5]
def baseStart_7032931 : Nat := 118140960795 + 7032931 * 2 ^ 59
def prefixEnd_7032931 : Nat := 4983230072969 + 3 ^ 40 * 7032931 * 2
def baseEnd_7032931 : Nat := 401252668100658706535405

theorem tailTrace_7032931 : CollatzResearch.WordTrace tailWord_7032931 prefixEnd_7032931 401252668100658706535405 := by
  unfold tailWord_7032931
  simp only [CollatzResearch.WordTrace]
  refine ⟨256512066883899590833146647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171008044589266393888764431 256512066883899590833146647)
  ·
    refine ⟨384768100325849386249719971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256512066883899590833146647 384768100325849386249719971)
    ·
      refine ⟨577152150488774079374579957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384768100325849386249719971 577152150488774079374579957)
      ·
        refine ⟨54108014108322569941366871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 577152150488774079374579957 54108014108322569941366871)
        ·
          refine ⟨81162021162483854912050307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54108014108322569941366871 81162021162483854912050307)
          ·
            refine ⟨121743031743725782368075461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81162021162483854912050307 121743031743725782368075461)
            ·
              refine ⟨22826818451948584194014149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121743031743725782368075461 22826818451948584194014149)
              ·
                refine ⟨4280028459740359536377653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22826818451948584194014149 4280028459740359536377653)
                ·
                  refine ⟨401252668100658706535405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4280028459740359536377653 401252668100658706535405)
                  ·
                    rfl

theorem cell23_7032931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 5].length) (baseStart_7032931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032931 prefixEnd_7032931 := by exact prefixLift 7032931
  have htrace : WordTrace (prefixWord ++ tailWord_7032931) baseStart_7032931 baseEnd_7032931 := by
    simpa [prefixWord, tailWord_7032931, baseEnd_7032931] using wordTrace_append hprefix tailTrace_7032931
  have hstable : (prefixWord ++ tailWord_7032931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032931).length < 2 ^ (prefixWord ++ tailWord_7032931).sum := by decide
  have hdescent : baseEnd_7032931 < baseStart_7032931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032941 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7032941 : Nat := 118140960795 + 7032941 * 2 ^ 59
def prefixEnd_7032941 : Nat := 4983230072969 + 3 ^ 40 * 7032941 * 2
def baseEnd_7032941 : Nat := 3611279147712473319693599

theorem tailTrace_7032941 : CollatzResearch.WordTrace tailWord_7032941 prefixEnd_7032941 3611279147712473319693599 := by
  unfold tailWord_7032941
  simp only [CollatzResearch.WordTrace]
  refine ⟨256512431613863362541010677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171008287742575575027340451 256512431613863362541010677)
  ·
    refine ⟨24048040463799690238219751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256512431613863362541010677 24048040463799690238219751)
    ·
      refine ⟨36072060695699535357329627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048040463799690238219751 36072060695699535357329627)
      ·
        refine ⟨54108091043549303035994441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36072060695699535357329627 54108091043549303035994441)
        ·
          refine ⟨40581068282661977276995831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54108091043549303035994441 40581068282661977276995831)
          ·
            refine ⟨60871602423992965915493747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40581068282661977276995831 60871602423992965915493747)
            ·
              refine ⟨91307403635989448873240621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60871602423992965915493747 91307403635989448873240621)
              ·
                refine ⟨34240276363496043327465233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91307403635989448873240621 34240276363496043327465233)
                ·
                  refine ⟨25680207272622032495598925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34240276363496043327465233 25680207272622032495598925)
                  ·
                    refine ⟨9630077727233262185849597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25680207272622032495598925 9630077727233262185849597)
                    ·
                      refine ⟨3611279147712473319693599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630077727233262185849597 3611279147712473319693599)
                      ·
                        rfl

theorem cell23_7032941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7032941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032941 prefixEnd_7032941 := by exact prefixLift 7032941
  have htrace : WordTrace (prefixWord ++ tailWord_7032941) baseStart_7032941 baseEnd_7032941 := by
    simpa [prefixWord, tailWord_7032941, baseEnd_7032941] using wordTrace_append hprefix tailTrace_7032941
  have hstable : (prefixWord ++ tailWord_7032941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032941).length < 2 ^ (prefixWord ++ tailWord_7032941).sum := by decide
  have hdescent : baseEnd_7032941 < baseStart_7032941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032942 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_7032942 : Nat := 118140960795 + 7032942 * 2 ^ 59
def prefixEnd_7032942 : Nat := 4983230072969 + 3 ^ 40 * 7032942 * 2
def baseEnd_7032942 : Nat := 3611279661193127815781095

theorem tailTrace_7032942 : CollatzResearch.WordTrace tailWord_7032942 prefixEnd_7032942 3611279661193127815781095 := by
  unfold tailWord_7032942
  simp only [CollatzResearch.WordTrace]
  refine ⟨32064058510857467463974635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171008312057906493141198053 32064058510857467463974635)
  ·
    refine ⟨48096087766286201195961953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32064058510857467463974635 48096087766286201195961953)
    ·
      refine ⟨36072065824714650896971465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48096087766286201195961953 36072065824714650896971465)
      ·
        refine ⟨27054049368535988172728599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36072065824714650896971465 27054049368535988172728599)
        ·
          refine ⟨40581074052803982259092899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27054049368535988172728599 40581074052803982259092899)
          ·
            refine ⟨60871611079205973388639349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40581074052803982259092899 60871611079205973388639349)
            ·
              refine ⟨5706713538675560005184939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60871611079205973388639349 5706713538675560005184939)
              ·
                refine ⟨8560070308013340007777409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706713538675560005184939 8560070308013340007777409)
                ·
                  refine ⟨6420052731010005005833057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560070308013340007777409 6420052731010005005833057)
                  ·
                    refine ⟨4815039548257503754374793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420052731010005005833057 4815039548257503754374793)
                    ·
                      refine ⟨3611279661193127815781095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815039548257503754374793 3611279661193127815781095)
                      ·
                        rfl

theorem cell23_7032942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_7032942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032942 prefixEnd_7032942 := by exact prefixLift 7032942
  have htrace : WordTrace (prefixWord ++ tailWord_7032942) baseStart_7032942 baseEnd_7032942 := by
    simpa [prefixWord, tailWord_7032942, baseEnd_7032942] using wordTrace_append hprefix tailTrace_7032942
  have hstable : (prefixWord ++ tailWord_7032942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032942).length < 2 ^ (prefixWord ++ tailWord_7032942).sum := by decide
  have hdescent : baseEnd_7032942 < baseStart_7032942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032944 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_7032944 : Nat := 118140960795 + 7032944 * 2 ^ 59
def prefixEnd_7032944 : Nat := 4983230072969 + 3 ^ 40 * 7032944 * 2
def baseEnd_7032944 : Nat := 1203760229384812269318695

theorem tailTrace_7032944 : CollatzResearch.WordTrace tailWord_7032944 prefixEnd_7032944 1203760229384812269318695 := by
  unfold tailWord_7032944
  simp only [CollatzResearch.WordTrace]
  refine ⟨128256270516426247026684943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171008360688568329368913257 128256270516426247026684943)
  ·
    refine ⟨192384405774639370540027415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128256270516426247026684943 192384405774639370540027415)
    ·
      refine ⟨288576608661959055810041123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192384405774639370540027415 288576608661959055810041123)
      ·
        refine ⟨432864912992938583715061685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288576608661959055810041123 432864912992938583715061685)
        ·
          refine ⟨40581085593087992223287033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432864912992938583715061685 40581085593087992223287033)
          ·
            refine ⟨30435814194815994167465275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40581085593087992223287033 30435814194815994167465275)
            ·
              refine ⟨45653721292223991251197913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30435814194815994167465275 45653721292223991251197913)
              ·
                refine ⟨34240290969167993438398435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45653721292223991251197913 34240290969167993438398435)
                ·
                  refine ⟨51360436453751990157597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34240290969167993438398435 51360436453751990157597653)
                  ·
                    refine ⟨1203760229384812269318695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51360436453751990157597653 1203760229384812269318695)
                    ·
                      rfl

theorem cell23_7032944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_7032944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032944 prefixEnd_7032944 := by exact prefixLift 7032944
  have htrace : WordTrace (prefixWord ++ tailWord_7032944) baseStart_7032944 baseEnd_7032944 := by
    simpa [prefixWord, tailWord_7032944, baseEnd_7032944] using wordTrace_append hprefix tailTrace_7032944
  have hstable : (prefixWord ++ tailWord_7032944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032944).length < 2 ^ (prefixWord ++ tailWord_7032944).sum := by decide
  have hdescent : baseEnd_7032944 < baseStart_7032944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032981 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_7032981 : Nat := 118140960795 + 7032981 * 2 ^ 59
def prefixEnd_7032981 : Nat := 4983230072969 + 3 ^ 40 * 7032981 * 2
def baseEnd_7032981 : Nat := 3611299686938653163193415

theorem tailTrace_7032981 : CollatzResearch.WordTrace tailWord_7032981 prefixEnd_7032981 3611299686938653163193415 := by
  unfold tailWord_7032981
  simp only [CollatzResearch.WordTrace]
  refine ⟨256513890533718449372466797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171009260355812299581644531 256513890533718449372466797)
  ·
    refine ⟨96192708950144418514675049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256513890533718449372466797 96192708950144418514675049)
    ·
      refine ⟨72144531712608313886006287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96192708950144418514675049 72144531712608313886006287)
      ·
        refine ⟨108216797568912470829009431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72144531712608313886006287 108216797568912470829009431)
        ·
          refine ⟨162325196353368706243514147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108216797568912470829009431 162325196353368706243514147)
          ·
            refine ⟨243487794530053059365271221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162325196353368706243514147 243487794530053059365271221)
            ·
              refine ⟨22826980737192474315494177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243487794530053059365271221 22826980737192474315494177)
              ·
                refine ⟨17120235552894355736620633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22826980737192474315494177 17120235552894355736620633)
                ·
                  refine ⟨12840176664670766802465475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17120235552894355736620633 12840176664670766802465475)
                  ·
                    refine ⟨19260264997006150203698213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12840176664670766802465475 19260264997006150203698213)
                    ·
                      refine ⟨3611299686938653163193415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19260264997006150203698213 3611299686938653163193415)
                      ·
                        rfl

theorem cell23_7032981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_7032981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032981 prefixEnd_7032981 := by exact prefixLift 7032981
  have htrace : WordTrace (prefixWord ++ tailWord_7032981) baseStart_7032981 baseEnd_7032981 := by
    simpa [prefixWord, tailWord_7032981, baseEnd_7032981] using wordTrace_append hprefix tailTrace_7032981
  have hstable : (prefixWord ++ tailWord_7032981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032981).length < 2 ^ (prefixWord ++ tailWord_7032981).sum := by decide
  have hdescent : baseEnd_7032981 < baseStart_7032981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033038 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_7033038 : Nat := 118140960795 + 7033038 * 2 ^ 59
def prefixEnd_7033038 : Nat := 4983230072969 + 3 ^ 40 * 7033038 * 2
def baseEnd_7033038 : Nat := 401258772815106604464517

theorem tailTrace_7033038 : CollatzResearch.WordTrace tailWord_7033038 prefixEnd_7033038 401258772815106604464517 := by
  unfold tailWord_7033038
  simp only [CollatzResearch.WordTrace]
  refine ⟨32064496186813993513411471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171010646329674632071527845 32064496186813993513411471)
  ·
    refine ⟨48096744280220990270117207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32064496186813993513411471 48096744280220990270117207)
    ·
      refine ⟨72145116420331485405175811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48096744280220990270117207 72145116420331485405175811)
      ·
        refine ⟨108217674630497228107763717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72145116420331485405175811 108217674630497228107763717)
        ·
          refine ⟨20290813993218230270205697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108217674630497228107763717 20290813993218230270205697)
          ·
            refine ⟨15218110494913672702654273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20290813993218230270205697 15218110494913672702654273)
            ·
              refine ⟨11413582871185254526990705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15218110494913672702654273 11413582871185254526990705)
              ·
                refine ⟨8560187153388940895243029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11413582871185254526990705 8560187153388940895243029)
                ·
                  refine ⟨401258772815106604464517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8560187153388940895243029 401258772815106604464517)
                  ·
                    rfl

theorem cell23_7033038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_7033038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033038 prefixEnd_7033038 := by exact prefixLift 7033038
  have htrace : WordTrace (prefixWord ++ tailWord_7033038) baseStart_7033038 baseEnd_7033038 := by
    simpa [prefixWord, tailWord_7033038, baseEnd_7033038] using wordTrace_append hprefix tailTrace_7033038
  have hstable : (prefixWord ++ tailWord_7033038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033038).length < 2 ^ (prefixWord ++ tailWord_7033038).sum := by decide
  have hdescent : baseEnd_7033038 < baseStart_7033038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033042 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7033042 : Nat := 118140960795 + 7033042 * 2 ^ 59
def prefixEnd_7033042 : Nat := 4983230072969 + 3 ^ 40 * 7033042 * 2
def baseEnd_7033042 : Nat := 1203777003086192474843545

theorem tailTrace_7033042 : CollatzResearch.WordTrace tailWord_7033042 prefixEnd_7033042 1203777003086192474843545 := by
  unfold tailWord_7033042
  simp only [CollatzResearch.WordTrace]
  refine ⟨64129028846624364197609345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171010743590998304526958253 64129028846624364197609345)
  ·
    refine ⟨48096771634968273148207009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64129028846624364197609345 48096771634968273148207009)
    ·
      refine ⟨36072578726226204861155257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48096771634968273148207009 36072578726226204861155257)
      ·
        refine ⟨27054434044669653645866443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36072578726226204861155257 27054434044669653645866443)
        ·
          refine ⟨40581651067004480468799665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27054434044669653645866443 40581651067004480468799665)
          ·
            refine ⟨30436238300253360351599749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40581651067004480468799665 30436238300253360351599749)
            ·
              refine ⟨5706794681297505065924953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30436238300253360351599749 5706794681297505065924953)
              ·
                refine ⟨4280096010973128799443715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706794681297505065924953 4280096010973128799443715)
                ·
                  refine ⟨6420144016459693199165573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280096010973128799443715 6420144016459693199165573)
                  ·
                    refine ⟨1203777003086192474843545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420144016459693199165573 1203777003086192474843545)
                    ·
                      rfl

theorem cell23_7033042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7033042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033042 prefixEnd_7033042 := by exact prefixLift 7033042
  have htrace : WordTrace (prefixWord ++ tailWord_7033042) baseStart_7033042 baseEnd_7033042 := by
    simpa [prefixWord, tailWord_7033042, baseEnd_7033042] using wordTrace_append hprefix tailTrace_7033042
  have hstable : (prefixWord ++ tailWord_7033042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033042).length < 2 ^ (prefixWord ++ tailWord_7033042).sum := by decide
  have hdescent : baseEnd_7033042 < baseStart_7033042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033082 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3]
def baseStart_7033082 : Nat := 118140960795 + 7033082 * 2 ^ 59
def prefixEnd_7033082 : Nat := 4983230072969 + 3 ^ 40 * 7033082 * 2
def baseEnd_7033082 : Nat := 3611351548484757268030451

theorem tailTrace_7033082 : CollatzResearch.WordTrace tailWord_7033082 prefixEnd_7033082 3611351548484757268030451 := by
  unfold tailWord_7033082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64129393576588135905473375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171011716204235029081262333 64129393576588135905473375)
  ·
    refine ⟨96194090364882203858210063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64129393576588135905473375 96194090364882203858210063)
    ·
      refine ⟨144291135547323305787315095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96194090364882203858210063 144291135547323305787315095)
      ·
        refine ⟨216436703320984958680972643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144291135547323305787315095 216436703320984958680972643)
        ·
          refine ⟨324655054981477438021458965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216436703320984958680972643 324655054981477438021458965)
          ·
            refine ⟨15218205702256754907255889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324655054981477438021458965 15218205702256754907255889)
            ·
              refine ⟨11413654276692566180441917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15218205702256754907255889 11413654276692566180441917)
              ·
                refine ⟨4280120353759712317665719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11413654276692566180441917 4280120353759712317665719)
                ·
                  refine ⟨6420180530639568476498579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280120353759712317665719 6420180530639568476498579)
                  ·
                    refine ⟨9630270795959352714747869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420180530639568476498579 9630270795959352714747869)
                    ·
                      refine ⟨3611351548484757268030451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630270795959352714747869 3611351548484757268030451)
                      ·
                        rfl

theorem cell23_7033082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_7033082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033082 prefixEnd_7033082 := by exact prefixLift 7033082
  have htrace : WordTrace (prefixWord ++ tailWord_7033082) baseStart_7033082 baseEnd_7033082 := by
    simpa [prefixWord, tailWord_7033082, baseEnd_7033082] using wordTrace_append hprefix tailTrace_7033082
  have hstable : (prefixWord ++ tailWord_7033082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033082).length < 2 ^ (prefixWord ++ tailWord_7033082).sum := by decide
  have hdescent : baseEnd_7033082 < baseStart_7033082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033091 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5]
def baseStart_7033091 : Nat := 118140960795 + 7033091 * 2 ^ 59
def prefixEnd_7033091 : Nat := 4983230072969 + 3 ^ 40 * 7033091 * 2
def baseEnd_7033091 : Nat := 3611356169810647732817909

theorem tailTrace_7033091 : CollatzResearch.WordTrace tailWord_7033091 prefixEnd_7033091 3611356169810647732817909 := by
  unfold tailWord_7033091
  simp only [CollatzResearch.WordTrace]
  refine ⟨256517902563319938158971127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171011935042213292105980751 256517902563319938158971127)
  ·
    refine ⟨384776853844979907238456691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256517902563319938158971127 384776853844979907238456691)
    ·
      refine ⟨577165280767469860857685037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384776853844979907238456691 577165280767469860857685037)
      ·
        refine ⟨216436980287801197821631889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577165280767469860857685037 216436980287801197821631889)
        ·
          refine ⟨162327735215850898366223917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216436980287801197821631889 162327735215850898366223917)
          ·
            refine ⟨60872900705944086887333969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162327735215850898366223917 60872900705944086887333969)
            ·
              refine ⟨45654675529458065165500477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60872900705944086887333969 45654675529458065165500477)
              ·
                refine ⟨17120503323546774437062679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45654675529458065165500477 17120503323546774437062679)
                ·
                  refine ⟨25680754985320161655594019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17120503323546774437062679 25680754985320161655594019)
                  ·
                    refine ⟨38521132477980242483391029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25680754985320161655594019 38521132477980242483391029)
                    ·
                      refine ⟨3611356169810647732817909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38521132477980242483391029 3611356169810647732817909)
                      ·
                        rfl

theorem cell23_7033091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_7033091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033091 prefixEnd_7033091 := by exact prefixLift 7033091
  have htrace : WordTrace (prefixWord ++ tailWord_7033091) baseStart_7033091 baseEnd_7033091 := by
    simpa [prefixWord, tailWord_7033091, baseEnd_7033091] using wordTrace_append hprefix tailTrace_7033091
  have hstable : (prefixWord ++ tailWord_7033091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033091).length < 2 ^ (prefixWord ++ tailWord_7033091).sum := by decide
  have hdescent : baseEnd_7033091 < baseStart_7033091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033105 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_7033105 : Nat := 118140960795 + 7033105 * 2 ^ 59
def prefixEnd_7033105 : Nat := 4983230072969 + 3 ^ 40 * 7033105 * 2
def baseEnd_7033105 : Nat := 3611363358539810678042845

theorem tailTrace_7033105 : CollatzResearch.WordTrace tailWord_7033105 prefixEnd_7033105 3611363358539810678042845 := by
  unfold tailWord_7033105
  simp only [CollatzResearch.WordTrace]
  refine ⟨256518413185269218549980769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171012275456846145699987179 256518413185269218549980769)
  ·
    refine ⟨192388809888951913912485577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256518413185269218549980769 192388809888951913912485577)
    ·
      refine ⟨144291607416713935434364183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192388809888951913912485577 144291607416713935434364183)
      ·
        refine ⟨216437411125070903151546275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144291607416713935434364183 216437411125070903151546275)
        ·
          refine ⟨324656116687606354727319413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216437411125070903151546275 324656116687606354727319413)
          ·
            refine ⟨30436510939463095755686195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324656116687606354727319413 30436510939463095755686195)
            ·
              refine ⟨45654766409194643633529293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30436510939463095755686195 45654766409194643633529293)
              ·
                refine ⟨17120537403447991362573485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45654766409194643633529293 17120537403447991362573485)
                ·
                  refine ⟨6420201526292996760965057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17120537403447991362573485 6420201526292996760965057)
                  ·
                    refine ⟨4815151144719747570723793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420201526292996760965057 4815151144719747570723793)
                    ·
                      refine ⟨3611363358539810678042845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815151144719747570723793 3611363358539810678042845)
                      ·
                        rfl

theorem cell23_7033105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_7033105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033105 prefixEnd_7033105 := by exact prefixLift 7033105
  have htrace : WordTrace (prefixWord ++ tailWord_7033105) baseStart_7033105 baseEnd_7033105 := by
    simpa [prefixWord, tailWord_7033105, baseEnd_7033105] using wordTrace_append hprefix tailTrace_7033105
  have hstable : (prefixWord ++ tailWord_7033105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033105).length < 2 ^ (prefixWord ++ tailWord_7033105).sum := by decide
  have hdescent : baseEnd_7033105 < baseStart_7033105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033122 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_7033122 : Nat := 118140960795 + 7033122 * 2 ^ 59
def prefixEnd_7033122 : Nat := 4983230072969 + 3 ^ 40 * 7033122 * 2
def baseEnd_7033122 : Nat := 3611372087710937111530267

theorem tailTrace_7033122 : CollatzResearch.WordTrace tailWord_7033122 prefixEnd_7033122 3611372087710937111530267 := by
  unfold tailWord_7033122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64129758306551907613337405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171012688817471753635566413 64129758306551907613337405)
  ·
    refine ⟨24048659364956965355001527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64129758306551907613337405 24048659364956965355001527)
    ·
      refine ⟨36072989047435448032502291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048659364956965355001527 36072989047435448032502291)
      ·
        refine ⟨54109483571153172048753437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36072989047435448032502291 54109483571153172048753437)
        ·
          refine ⟨20291056339182439518282539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54109483571153172048753437 20291056339182439518282539)
          ·
            refine ⟨30436584508773659277423809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20291056339182439518282539 30436584508773659277423809)
            ·
              refine ⟨22827438381580244458067857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30436584508773659277423809 22827438381580244458067857)
              ·
                refine ⟨17120578786185183343550893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22827438381580244458067857 17120578786185183343550893)
                ·
                  refine ⟨6420217044819443753831585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17120578786185183343550893 6420217044819443753831585)
                  ·
                    refine ⟨4815162783614582815373689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420217044819443753831585 4815162783614582815373689)
                    ·
                      refine ⟨3611372087710937111530267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815162783614582815373689 3611372087710937111530267)
                      ·
                        rfl

theorem cell23_7033122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_7033122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033122 prefixEnd_7033122 := by exact prefixLift 7033122
  have htrace : WordTrace (prefixWord ++ tailWord_7033122) baseStart_7033122 baseEnd_7033122 := by
    simpa [prefixWord, tailWord_7033122, baseEnd_7033122] using wordTrace_append hprefix tailTrace_7033122
  have hstable : (prefixWord ++ tailWord_7033122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033122).length < 2 ^ (prefixWord ++ tailWord_7033122).sum := by decide
  have hdescent : baseEnd_7033122 < baseStart_7033122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033128 : List Nat := [2, 1, 5, 1, 3, 1, 1, 9]
def baseStart_7033128 : Nat := 118140960795 + 7033128 * 2 ^ 59
def prefixEnd_7033128 : Nat := 4983230072969 + 3 ^ 40 * 7033128 * 2
def baseEnd_7033128 : Nat := 133754635873883855113157

theorem tailTrace_7033128 : CollatzResearch.WordTrace tailWord_7033128 prefixEnd_7033128 133754635873883855113157 := by
  unfold tailWord_7033128
  simp only [CollatzResearch.WordTrace]
  refine ⟨128259626032092946739034019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171012834709457262318712025 128259626032092946739034019)
  ·
    refine ⟨192389439048139420108551029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128259626032092946739034019 192389439048139420108551029)
    ·
      refine ⟨18036509910763070635176659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192389439048139420108551029 18036509910763070635176659)
      ·
        refine ⟨27054764866144605952764989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18036509910763070635176659 27054764866144605952764989)
        ·
          refine ⟨10145536824804227232286871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27054764866144605952764989 10145536824804227232286871)
          ·
            refine ⟨15218305237206340848430307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145536824804227232286871 15218305237206340848430307)
            ·
              refine ⟨22827457855809511272645461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15218305237206340848430307 22827457855809511272645461)
              ·
                refine ⟨133754635873883855113157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22827457855809511272645461 133754635873883855113157)
                ·
                  rfl

theorem cell23_7033128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 9].length) (baseStart_7033128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033128 prefixEnd_7033128 := by exact prefixLift 7033128
  have htrace : WordTrace (prefixWord ++ tailWord_7033128) baseStart_7033128 baseEnd_7033128 := by
    simpa [prefixWord, tailWord_7033128, baseEnd_7033128] using wordTrace_append hprefix tailTrace_7033128
  have hstable : (prefixWord ++ tailWord_7033128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033128).length < 2 ^ (prefixWord ++ tailWord_7033128).sum := by decide
  have hdescent : baseEnd_7033128 < baseStart_7033128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033133 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7033133 : Nat := 118140960795 + 7033133 * 2 ^ 59
def prefixEnd_7033133 : Nat := 4983230072969 + 3 ^ 40 * 7033133 * 2
def baseEnd_7033133 : Nat := 3611377735998136568492717

theorem tailTrace_7033133 : CollatzResearch.WordTrace tailWord_7033133 prefixEnd_7033133 3611377735998136568492717 := by
  unfold tailWord_7033133
  simp only [CollatzResearch.WordTrace]
  refine ⟨256519434429167779332000053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171012956286111852888000035 256519434429167779332000053)
  ·
    refine ⟨24048696977734479312375005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256519434429167779332000053 24048696977734479312375005)
    ·
      refine ⟨9018261366650429742140627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24048696977734479312375005 9018261366650429742140627)
      ·
        refine ⟨13527392049975644613210941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018261366650429742140627 13527392049975644613210941)
        ·
          refine ⟨5072772018740866729954103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13527392049975644613210941 5072772018740866729954103)
          ·
            refine ⟨7609158028111300094931155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072772018740866729954103 7609158028111300094931155)
            ·
              refine ⟨11413737042166950142396733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609158028111300094931155 11413737042166950142396733)
              ·
                refine ⟨4280151390812606303398775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11413737042166950142396733 4280151390812606303398775)
                ·
                  refine ⟨6420227086218909455098163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280151390812606303398775 6420227086218909455098163)
                  ·
                    refine ⟨9630340629328364182647245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420227086218909455098163 9630340629328364182647245)
                    ·
                      refine ⟨3611377735998136568492717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630340629328364182647245 3611377735998136568492717)
                      ·
                        rfl

theorem cell23_7033133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7033133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033133 prefixEnd_7033133 := by exact prefixLift 7033133
  have htrace : WordTrace (prefixWord ++ tailWord_7033133) baseStart_7033133 baseEnd_7033133 := by
    simpa [prefixWord, tailWord_7033133, baseEnd_7033133] using wordTrace_append hprefix tailTrace_7033133
  have hstable : (prefixWord ++ tailWord_7033133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033133).length < 2 ^ (prefixWord ++ tailWord_7033133).sum := by decide
  have hdescent : baseEnd_7033133 < baseStart_7033133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033151 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_7033151 : Nat := 118140960795 + 7033151 * 2 ^ 59
def prefixEnd_7033151 : Nat := 4983230072969 + 3 ^ 40 * 7033151 * 2
def baseEnd_7033151 : Nat := 3611386978649917498067633

theorem tailTrace_7033151 : CollatzResearch.WordTrace tailWord_7033151 prefixEnd_7033151 3611386978649917498067633 := by
  unfold tailWord_7033151
  simp only [CollatzResearch.WordTrace]
  refine ⟨256520090943102568406155307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171013393962068378937436871 256520090943102568406155307)
  ·
    refine ⟨384780136414653852609232961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256520090943102568406155307 384780136414653852609232961)
    ·
      refine ⟨288585102310990389456924721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384780136414653852609232961 288585102310990389456924721)
      ·
        refine ⟨216438826733242792092693541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288585102310990389456924721 216438826733242792092693541)
        ·
          refine ⟨40582280012483023517380039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216438826733242792092693541 40582280012483023517380039)
          ·
            refine ⟨60873420018724535276070059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40582280012483023517380039 60873420018724535276070059)
            ·
              refine ⟨91310130028086802914105089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60873420018724535276070059 91310130028086802914105089)
              ·
                refine ⟨68482597521065102185578817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91310130028086802914105089 68482597521065102185578817)
                ·
                  refine ⟨51361948140798826639184113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68482597521065102185578817 51361948140798826639184113)
                  ·
                    refine ⟨38521461105599119979388085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51361948140798826639184113 38521461105599119979388085)
                    ·
                      refine ⟨3611386978649917498067633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38521461105599119979388085 3611386978649917498067633)
                      ·
                        rfl

theorem cell23_7033151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_7033151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033151 prefixEnd_7033151 := by exact prefixLift 7033151
  have htrace : WordTrace (prefixWord ++ tailWord_7033151) baseStart_7033151 baseEnd_7033151 := by
    simpa [prefixWord, tailWord_7033151, baseEnd_7033151] using wordTrace_append hprefix tailTrace_7033151
  have hstable : (prefixWord ++ tailWord_7033151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033151).length < 2 ^ (prefixWord ++ tailWord_7033151).sum := by decide
  have hdescent : baseEnd_7033151 < baseStart_7033151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033156 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7033156 : Nat := 118140960795 + 7033156 * 2 ^ 59
def prefixEnd_7033156 : Nat := 4983230072969 + 3 ^ 40 * 7033156 * 2
def baseEnd_7033156 : Nat := 3611389546053189978505111

theorem tailTrace_7033156 : CollatzResearch.WordTrace tailWord_7033156 prefixEnd_7033156 3611389546053189978505111 := by
  unfold tailWord_7033156
  simp only [CollatzResearch.WordTrace]
  refine ⟨128260136654042227130043661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171013515538722969506724881 128260136654042227130043661)
  ·
    refine ⟨48097551245265835173766373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128260136654042227130043661 48097551245265835173766373)
    ·
      refine ⟨9018290858487344095081195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48097551245265835173766373 9018290858487344095081195)
      ·
        refine ⟨13527436287731016142621793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018290858487344095081195 13527436287731016142621793)
        ·
          refine ⟨10145577215798262106966345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13527436287731016142621793 10145577215798262106966345)
          ·
            refine ⟨7609182911848696580224759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10145577215798262106966345 7609182911848696580224759)
            ·
              refine ⟨11413774367773044870337139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609182911848696580224759 11413774367773044870337139)
              ·
                refine ⟨17120661551659567305505709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11413774367773044870337139 17120661551659567305505709)
                ·
                  refine ⟨6420248081872337739564641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17120661551659567305505709 6420248081872337739564641)
                  ·
                    refine ⟨4815186061404253304673481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420248081872337739564641 4815186061404253304673481)
                    ·
                      refine ⟨3611389546053189978505111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815186061404253304673481 3611389546053189978505111)
                      ·
                        rfl

theorem cell23_7033156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7033156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033156 prefixEnd_7033156 := by exact prefixLift 7033156
  have htrace : WordTrace (prefixWord ++ tailWord_7033156) baseStart_7033156 baseEnd_7033156 := by
    simpa [prefixWord, tailWord_7033156, baseEnd_7033156] using wordTrace_append hprefix tailTrace_7033156
  have hstable : (prefixWord ++ tailWord_7033156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033156).length < 2 ^ (prefixWord ++ tailWord_7033156).sum := by decide
  have hdescent : baseEnd_7033156 < baseStart_7033156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033161 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_7033161 : Nat := 118140960795 + 7033161 * 2 ^ 59
def prefixEnd_7033161 : Nat := 4983230072969 + 3 ^ 40 * 7033161 * 2
def baseEnd_7033161 : Nat := 3611392113456462458942587

theorem tailTrace_7033161 : CollatzResearch.WordTrace tailWord_7033161 prefixEnd_7033161 3611392113456462458942587 := by
  unfold tailWord_7033161
  simp only [CollatzResearch.WordTrace]
  refine ⟨256520455673066340114019337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171013637115377560076012891 256520455673066340114019337)
  ·
    refine ⟨192390341754799755085514503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256520455673066340114019337 192390341754799755085514503)
    ·
      refine ⟨288585512632199632628271755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192390341754799755085514503 288585512632199632628271755)
      ·
        refine ⟨432878268948299448942407633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288585512632199632628271755 432878268948299448942407633)
        ·
          refine ⟨324658701711224586706805725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432878268948299448942407633 324658701711224586706805725)
          ·
            refine ⟨121747013141709220015052147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324658701711224586706805725 121747013141709220015052147)
            ·
              refine ⟨182620519712563830022578221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121747013141709220015052147 182620519712563830022578221)
              ·
                refine ⟨68482694892211436258466833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182620519712563830022578221 68482694892211436258466833)
                ·
                  refine ⟨51362021169158577193850125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68482694892211436258466833 51362021169158577193850125)
                  ·
                    refine ⟨19260757938434466447693797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51362021169158577193850125 19260757938434466447693797)
                    ·
                      refine ⟨3611392113456462458942587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19260757938434466447693797 3611392113456462458942587)
                      ·
                        rfl

theorem cell23_7033161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_7033161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033161 prefixEnd_7033161 := by exact prefixLift 7033161
  have htrace : WordTrace (prefixWord ++ tailWord_7033161) baseStart_7033161 baseEnd_7033161 := by
    simpa [prefixWord, tailWord_7033161, baseEnd_7033161] using wordTrace_append hprefix tailTrace_7033161
  have hstable : (prefixWord ++ tailWord_7033161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033161).length < 2 ^ (prefixWord ++ tailWord_7033161).sum := by decide
  have hdescent : baseEnd_7033161 < baseStart_7033161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033172 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_7033172 : Nat := 118140960795 + 7033172 * 2 ^ 59
def prefixEnd_7033172 : Nat := 4983230072969 + 3 ^ 40 * 7033172 * 2
def baseEnd_7033172 : Nat := 3611397761743661915905037

theorem tailTrace_7033172 : CollatzResearch.WordTrace tailWord_7033172 prefixEnd_7033172 3611397761743661915905037 := by
  unfold tailWord_7033172
  simp only [CollatzResearch.WordTrace]
  refine ⟨128260428438013244496334885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171013904584017659328446513 128260428438013244496334885)
  ·
    refine ⟨24048830332127483343062791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128260428438013244496334885 24048830332127483343062791)
    ·
      refine ⟨36073245498191225014594187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048830332127483343062791 36073245498191225014594187)
      ·
        refine ⟨54109868247286837521891281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36073245498191225014594187 54109868247286837521891281)
        ·
          refine ⟨40582401185465128141418461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54109868247286837521891281 40582401185465128141418461)
          ·
            refine ⟨15218400444549423053031923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40582401185465128141418461 15218400444549423053031923)
            ·
              refine ⟨22827600666824134579547885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15218400444549423053031923 22827600666824134579547885)
              ·
                refine ⟨8560350250059050467330457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22827600666824134579547885 8560350250059050467330457)
                ·
                  refine ⟨6420262687544287850497843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560350250059050467330457 6420262687544287850497843)
                  ·
                    refine ⟨9630394031316431775746765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420262687544287850497843 9630394031316431775746765)
                    ·
                      refine ⟨3611397761743661915905037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630394031316431775746765 3611397761743661915905037)
                      ·
                        rfl

theorem cell23_7033172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_7033172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033172 prefixEnd_7033172 := by exact prefixLift 7033172
  have htrace : WordTrace (prefixWord ++ tailWord_7033172) baseStart_7033172 baseEnd_7033172 := by
    simpa [prefixWord, tailWord_7033172, baseEnd_7033172] using wordTrace_append hprefix tailTrace_7033172
  have hstable : (prefixWord ++ tailWord_7033172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033172).length < 2 ^ (prefixWord ++ tailWord_7033172).sum := by decide
  have hdescent : baseEnd_7033172 < baseStart_7033172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033206 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7033206 : Nat := 118140960795 + 7033206 * 2 ^ 59
def prefixEnd_7033206 : Nat := 4983230072969 + 3 ^ 40 * 7033206 * 2
def baseEnd_7033206 : Nat := 3611415220085914782879881

theorem tailTrace_7033206 : CollatzResearch.WordTrace tailWord_7033206 prefixEnd_7033206 3611415220085914782879881 := by
  unfold tailWord_7033206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032631059868957049962967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171014731305268875199604981 16032631059868957049962967)
  ·
    refine ⟨24048946589803435574944451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16032631059868957049962967 24048946589803435574944451)
    ·
      refine ⟨36073419884705153362416677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048946589803435574944451 36073419884705153362416677)
      ·
        refine ⟨6763766228382216255453127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36073419884705153362416677 6763766228382216255453127)
        ·
          refine ⟨10145649342573324383179691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763766228382216255453127 10145649342573324383179691)
          ·
            refine ⟨15218474013859986574769537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145649342573324383179691 15218474013859986574769537)
            ·
              refine ⟨11413855510394989931077153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15218474013859986574769537 11413855510394989931077153)
              ·
                refine ⟨8560391632796242448307865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11413855510394989931077153 8560391632796242448307865)
                ·
                  refine ⟨6420293724597181836230899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560391632796242448307865 6420293724597181836230899)
                  ·
                    refine ⟨9630440586895772754346349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420293724597181836230899 9630440586895772754346349)
                    ·
                      refine ⟨3611415220085914782879881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630440586895772754346349 3611415220085914782879881)
                      ·
                        rfl

theorem cell23_7033206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7033206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033206 prefixEnd_7033206 := by exact prefixLift 7033206
  have htrace : WordTrace (prefixWord ++ tailWord_7033206) baseStart_7033206 baseEnd_7033206 := by
    simpa [prefixWord, tailWord_7033206, baseEnd_7033206] using wordTrace_append hprefix tailTrace_7033206
  have hstable : (prefixWord ++ tailWord_7033206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033206).length < 2 ^ (prefixWord ++ tailWord_7033206).sum := by decide
  have hdescent : baseEnd_7033206 < baseStart_7033206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033221 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_7033221 : Nat := 118140960795 + 7033221 * 2 ^ 59
def prefixEnd_7033221 : Nat := 4983230072969 + 3 ^ 40 * 7033221 * 2
def baseEnd_7033221 : Nat := 3611422922295732224192311

theorem tailTrace_7033221 : CollatzResearch.WordTrace tailWord_7033221 prefixEnd_7033221 3611422922295732224192311 := by
  unfold tailWord_7033221
  simp only [CollatzResearch.WordTrace]
  refine ⟨256522644052848970361203517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171015096035232646907469011 256522644052848970361203517)
  ·
    refine ⟨96195991519818363885451319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256522644052848970361203517 96195991519818363885451319)
    ·
      refine ⟨144293987279727545828176979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96195991519818363885451319 144293987279727545828176979)
      ·
        refine ⟨216440980919591318742265469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144293987279727545828176979 216440980919591318742265469)
        ·
          refine ⟨81165367844846744528349551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216440980919591318742265469 81165367844846744528349551)
          ·
            refine ⟨121748051767270116792524327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81165367844846744528349551 121748051767270116792524327)
            ·
              refine ⟨182622077650905175188786491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121748051767270116792524327 182622077650905175188786491)
              ·
                refine ⟨273933116476357762783179737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182622077650905175188786491 273933116476357762783179737)
                ·
                  refine ⟨205449837357268322087384803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273933116476357762783179737 205449837357268322087384803)
                  ·
                    refine ⟨308174756035902483131077205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205449837357268322087384803 308174756035902483131077205)
                    ·
                      refine ⟨3611422922295732224192311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 308174756035902483131077205 3611422922295732224192311)
                      ·
                        rfl

theorem cell23_7033221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_7033221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033221 prefixEnd_7033221 := by exact prefixLift 7033221
  have htrace : WordTrace (prefixWord ++ tailWord_7033221) baseStart_7033221 baseEnd_7033221 := by
    simpa [prefixWord, tailWord_7033221, baseEnd_7033221] using wordTrace_append hprefix tailTrace_7033221
  have hstable : (prefixWord ++ tailWord_7033221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033221).length < 2 ^ (prefixWord ++ tailWord_7033221).sum := by decide
  have hdescent : baseEnd_7033221 < baseStart_7033221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033228 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_7033228 : Nat := 118140960795 + 7033228 * 2 ^ 59
def prefixEnd_7033228 : Nat := 4983230072969 + 3 ^ 40 * 7033228 * 2
def baseEnd_7033228 : Nat := 3611426516660313696804779

theorem tailTrace_7033228 : CollatzResearch.WordTrace tailWord_7033228 prefixEnd_7033228 3611426516660313696804779 := by
  unfold tailWord_7033228
  simp only [CollatzResearch.WordTrace]
  refine ⟨128261449681911805278354169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171015266242549073704472225 128261449681911805278354169)
  ·
    refine ⟨96196087261433853958765627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128261449681911805278354169 96196087261433853958765627)
    ·
      refine ⟨144294130892150780938148441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96196087261433853958765627 144294130892150780938148441)
      ·
        refine ⟨108220598169113085703611331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144294130892150780938148441 108220598169113085703611331)
        ·
          refine ⟨162330897253669628555416997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108220598169113085703611331 162330897253669628555416997)
          ·
            refine ⟨30437043235063055354140687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162330897253669628555416997 30437043235063055354140687)
            ·
              refine ⟨45655564852594583031211031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30437043235063055354140687 45655564852594583031211031)
              ·
                refine ⟨68483347278891874546816547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45655564852594583031211031 68483347278891874546816547)
                ·
                  refine ⟨102725020918337811820224821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68483347278891874546816547 102725020918337811820224821)
                  ·
                    refine ⟨9630470711094169858146077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102725020918337811820224821 9630470711094169858146077)
                    ·
                      refine ⟨3611426516660313696804779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630470711094169858146077 3611426516660313696804779)
                      ·
                        rfl

theorem cell23_7033228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_7033228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033228 prefixEnd_7033228 := by exact prefixLift 7033228
  have htrace : WordTrace (prefixWord ++ tailWord_7033228) baseStart_7033228 baseEnd_7033228 := by
    simpa [prefixWord, tailWord_7033228, baseEnd_7033228] using wordTrace_append hprefix tailTrace_7033228
  have hstable : (prefixWord ++ tailWord_7033228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033228).length < 2 ^ (prefixWord ++ tailWord_7033228).sum := by decide
  have hdescent : baseEnd_7033228 < baseStart_7033228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033248 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_7033248 : Nat := 118140960795 + 7033248 * 2 ^ 59
def prefixEnd_7033248 : Nat := 4983230072969 + 3 ^ 40 * 7033248 * 2
def baseEnd_7033248 : Nat := 1203812262091134539518229

theorem tailTrace_7033248 : CollatzResearch.WordTrace tailWord_7033248 prefixEnd_7033248 1203812262091134539518229 := by
  unfold tailWord_7033248
  simp only [CollatzResearch.WordTrace]
  refine ⟨128261814411875576986218199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171015752549167435981624265 128261814411875576986218199)
  ·
    refine ⟨192392721617813365479327299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128261814411875576986218199 192392721617813365479327299)
    ·
      refine ⟨288589082426720048218990949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192392721617813365479327299 288589082426720048218990949)
      ·
        refine ⟨54110452955010009041060803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288589082426720048218990949 54110452955010009041060803)
        ·
          refine ⟨81165679432515013561591205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54110452955010009041060803 81165679432515013561591205)
          ·
            refine ⟨15218564893596565042798351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81165679432515013561591205 15218564893596565042798351)
            ·
              refine ⟨22827847340394847564197527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15218564893596565042798351 22827847340394847564197527)
              ·
                refine ⟨34241771010592271346296291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22827847340394847564197527 34241771010592271346296291)
                ·
                  refine ⟨51362656515888407019444437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34241771010592271346296291 51362656515888407019444437)
                  ·
                    refine ⟨1203812262091134539518229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51362656515888407019444437 1203812262091134539518229)
                    ·
                      rfl

theorem cell23_7033248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_7033248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033248 prefixEnd_7033248 := by exact prefixLift 7033248
  have htrace : WordTrace (prefixWord ++ tailWord_7033248) baseStart_7033248 baseEnd_7033248 := by
    simpa [prefixWord, tailWord_7033248, baseEnd_7033248] using wordTrace_append hprefix tailTrace_7033248
  have hstable : (prefixWord ++ tailWord_7033248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033248).length < 2 ^ (prefixWord ++ tailWord_7033248).sum := by decide
  have hdescent : baseEnd_7033248 < baseStart_7033248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033302 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7033302 : Nat := 118140960795 + 7033302 * 2 ^ 59
def prefixEnd_7033302 : Nat := 4983230072969 + 3 ^ 40 * 7033302 * 2
def baseEnd_7033302 : Nat := 3611464514228746407279439

theorem tailTrace_7033302 : CollatzResearch.WordTrace tailWord_7033302 prefixEnd_7033302 3611464514228746407279439 := by
  unfold tailWord_7033302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032849897847220074681385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171017065577037014129934773 16032849897847220074681385)
  ·
    refine ⟨12024637423385415056011039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16032849897847220074681385 12024637423385415056011039)
    ·
      refine ⟨18036956135078122584016559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12024637423385415056011039 18036956135078122584016559)
      ·
        refine ⟨27055434202617183876024839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18036956135078122584016559 27055434202617183876024839)
        ·
          refine ⟨40583151303925775814037259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27055434202617183876024839 40583151303925775814037259)
          ·
            refine ⟨60874726955888663721055889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40583151303925775814037259 60874726955888663721055889)
            ·
              refine ⟨45656045216916497790791917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60874726955888663721055889 45656045216916497790791917)
              ·
                refine ⟨17121016956343686671546969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45656045216916497790791917 17121016956343686671546969)
                ·
                  refine ⟨12840762717257765003660227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17121016956343686671546969 12840762717257765003660227)
                  ·
                    refine ⟨19261144075886647505490341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12840762717257765003660227 19261144075886647505490341)
                    ·
                      refine ⟨3611464514228746407279439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19261144075886647505490341 3611464514228746407279439)
                      ·
                        rfl

theorem cell23_7033302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7033302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033302 prefixEnd_7033302 := by exact prefixLift 7033302
  have htrace : WordTrace (prefixWord ++ tailWord_7033302) baseStart_7033302 baseEnd_7033302 := by
    simpa [prefixWord, tailWord_7033302, baseEnd_7033302] using wordTrace_append hprefix tailTrace_7033302
  have hstable : (prefixWord ++ tailWord_7033302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033302).length < 2 ^ (prefixWord ++ tailWord_7033302).sum := by decide
  have hdescent : baseEnd_7033302 < baseStart_7033302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033305 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_7033305 : Nat := 118140960795 + 7033305 * 2 ^ 59
def prefixEnd_7033305 : Nat := 4983230072969 + 3 ^ 40 * 7033305 * 2
def baseEnd_7033305 : Nat := 3611466054670709895541925

theorem tailTrace_7033305 : CollatzResearch.WordTrace tailWord_7033305 prefixEnd_7033305 3611466054670709895541925 := by
  unfold tailWord_7033305
  simp only [CollatzResearch.WordTrace]
  refine ⟨256525707784544652707261369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171017138523029768471507579 256525707784544652707261369)
  ·
    refine ⟨192394280838408489530446027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256525707784544652707261369 192394280838408489530446027)
    ·
      refine ⟨288591421257612734295669041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192394280838408489530446027 288591421257612734295669041)
      ·
        refine ⟨216443565943209550721751781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288591421257612734295669041 216443565943209550721751781)
        ·
          refine ⟨40583168614351790760328459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216443565943209550721751781 40583168614351790760328459)
          ·
            refine ⟨60874752921527686140492689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40583168614351790760328459 60874752921527686140492689)
            ·
              refine ⟨45656064691145764605369517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60874752921527686140492689 45656064691145764605369517)
              ·
                refine ⟨17121024259179661727013569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45656064691145764605369517 17121024259179661727013569)
                ·
                  refine ⟨12840768194384746295260177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17121024259179661727013569 12840768194384746295260177)
                  ·
                    refine ⟨9630576145788559721445133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12840768194384746295260177 9630576145788559721445133)
                    ·
                      refine ⟨3611466054670709895541925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630576145788559721445133 3611466054670709895541925)
                      ·
                        rfl

theorem cell23_7033305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_7033305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033305 prefixEnd_7033305 := by exact prefixLift 7033305
  have htrace : WordTrace (prefixWord ++ tailWord_7033305) baseStart_7033305 baseEnd_7033305 := by
    simpa [prefixWord, tailWord_7033305, baseEnd_7033305] using wordTrace_append hprefix tailTrace_7033305
  have hstable : (prefixWord ++ tailWord_7033305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033305).length < 2 ^ (prefixWord ++ tailWord_7033305).sum := by decide
  have hdescent : baseEnd_7033305 < baseStart_7033305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033322 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_7033322 : Nat := 118140960795 + 7033322 * 2 ^ 59
def prefixEnd_7033322 : Nat := 4983230072969 + 3 ^ 40 * 7033322 * 2
def baseEnd_7033322 : Nat := 3611474783841836329029347

theorem tailTrace_7033322 : CollatzResearch.WordTrace tailWord_7033322 prefixEnd_7033322 3611474783841836329029347 := by
  unfold tailWord_7033322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64131581956370766152657555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171017551883655376407086813 64131581956370766152657555)
  ·
    refine ⟨96197372934556149228986333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64131581956370766152657555 96197372934556149228986333)
    ·
      refine ⟨36074014850458555960869875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96197372934556149228986333 36074014850458555960869875)
      ·
        refine ⟨54111022275687833941304813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36074014850458555960869875 54111022275687833941304813)
        ·
          refine ⟨20291633353382937727989305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54111022275687833941304813 20291633353382937727989305)
          ·
            refine ⟨15218725015037203295991979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20291633353382937727989305 15218725015037203295991979)
            ·
              refine ⟨22828087522555804943987969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15218725015037203295991979 22828087522555804943987969)
              ·
                refine ⟨17121065641916853707990977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22828087522555804943987969 17121065641916853707990977)
                ·
                  refine ⟨12840799231437640280993233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17121065641916853707990977 12840799231437640280993233)
                  ·
                    refine ⟨9630599423578230210744925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12840799231437640280993233 9630599423578230210744925)
                    ·
                      refine ⟨3611474783841836329029347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630599423578230210744925 3611474783841836329029347)
                      ·
                        rfl

theorem cell23_7033322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_7033322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033322 prefixEnd_7033322 := by exact prefixLift 7033322
  have htrace : WordTrace (prefixWord ++ tailWord_7033322) baseStart_7033322 baseEnd_7033322 := by
    simpa [prefixWord, tailWord_7033322, baseEnd_7033322] using wordTrace_append hprefix tailTrace_7033322
  have hstable : (prefixWord ++ tailWord_7033322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033322).length < 2 ^ (prefixWord ++ tailWord_7033322).sum := by decide
  have hdescent : baseEnd_7033322 < baseStart_7033322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033325 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 8]
def baseStart_7033325 : Nat := 118140960795 + 7033325 * 2 ^ 59
def prefixEnd_7033325 : Nat := 4983230072969 + 3 ^ 40 * 7033325 * 2
def baseEnd_7033325 : Nat := 401275147142644424143537

theorem tailTrace_7033325 : CollatzResearch.WordTrace tailWord_7033325 prefixEnd_7033325 401275147142644424143537 := by
  unfold tailWord_7033325
  simp only [CollatzResearch.WordTrace]
  refine ⟨256526437244472196122989429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171017624829648130748659619 256526437244472196122989429)
  ·
    refine ⟨24049353491669268386530259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256526437244472196122989429 24049353491669268386530259)
    ·
      refine ⟨36074030237503902579795389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24049353491669268386530259 36074030237503902579795389)
      ·
        refine ⟨13527761339063963467423271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36074030237503902579795389 13527761339063963467423271)
        ·
          refine ⟨20291642008595945201134907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13527761339063963467423271 20291642008595945201134907)
          ·
            refine ⟨30437463012893917801702361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20291642008595945201134907 30437463012893917801702361)
            ·
              refine ⟨22828097259670438351276771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30437463012893917801702361 22828097259670438351276771)
              ·
                refine ⟨34242145889505657526915157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22828097259670438351276771 34242145889505657526915157)
                ·
                  refine ⟨401275147142644424143537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34242145889505657526915157 401275147142644424143537)
                  ·
                    rfl

theorem cell23_7033325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_7033325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033325 prefixEnd_7033325 := by exact prefixLift 7033325
  have htrace : WordTrace (prefixWord ++ tailWord_7033325) baseStart_7033325 baseEnd_7033325 := by
    simpa [prefixWord, tailWord_7033325, baseEnd_7033325] using wordTrace_append hprefix tailTrace_7033325
  have hstable : (prefixWord ++ tailWord_7033325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033325).length < 2 ^ (prefixWord ++ tailWord_7033325).sum := by decide
  have hdescent : baseEnd_7033325 < baseStart_7033325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033329 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 1, 4]
def baseStart_7033329 : Nat := 118140960795 + 7033329 * 2 ^ 59
def prefixEnd_7033329 : Nat := 4983230072969 + 3 ^ 40 * 7033329 * 2
def baseEnd_7033329 : Nat := 1203826126068805933880605

theorem tailTrace_7033329 : CollatzResearch.WordTrace tailWord_7033329 prefixEnd_7033329 1203826126068805933880605 := by
  unfold tailWord_7033329
  simp only [CollatzResearch.WordTrace]
  refine ⟨256526583136457704806135041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171017722090971803204090027 256526583136457704806135041)
  ·
    refine ⟨192394937352343278604601281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256526583136457704806135041 192394937352343278604601281)
    ·
      refine ⟨144296203014257458953450961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192394937352343278604601281 144296203014257458953450961)
      ·
        refine ⟨108222152260693094215088221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144296203014257458953450961 108222152260693094215088221)
        ·
          refine ⟨40583307097759910330658083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108222152260693094215088221 40583307097759910330658083)
          ·
            refine ⟨60874960646639865495987125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40583307097759910330658083 60874960646639865495987125)
            ·
              refine ⟨5707027560622487390248793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60874960646639865495987125 5707027560622487390248793)
              ·
                refine ⟨4280270670466865542686595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707027560622487390248793 4280270670466865542686595)
                ·
                  refine ⟨6420406005700298314029893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280270670466865542686595 6420406005700298314029893)
                  ·
                    refine ⟨1203826126068805933880605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420406005700298314029893 1203826126068805933880605)
                    ·
                      rfl

theorem cell23_7033329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_7033329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033329 prefixEnd_7033329 := by exact prefixLift 7033329
  have htrace : WordTrace (prefixWord ++ tailWord_7033329) baseStart_7033329 baseEnd_7033329 := by
    simpa [prefixWord, tailWord_7033329, baseEnd_7033329] using wordTrace_append hprefix tailTrace_7033329
  have hstable : (prefixWord ++ tailWord_7033329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033329).length < 2 ^ (prefixWord ++ tailWord_7033329).sum := by decide
  have hdescent : baseEnd_7033329 < baseStart_7033329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033355 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 3, 5]
def baseStart_7033355 : Nat := 118140960795 + 7033355 * 2 ^ 59
def prefixEnd_7033355 : Nat := 4983230072969 + 3 ^ 40 * 7033355 * 2
def baseEnd_7033355 : Nat := 1203830576234478233305565

theorem tailTrace_7033355 : CollatzResearch.WordTrace tailWord_7033355 prefixEnd_7033355 1203830576234478233305565 := by
  unfold tailWord_7033355
  simp only [CollatzResearch.WordTrace]
  refine ⟨256527531434363511246581519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171018354289575674164387679 256527531434363511246581519)
  ·
    refine ⟨384791297151545266869872279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256527531434363511246581519 384791297151545266869872279)
    ·
      refine ⟨577186945727317900304808419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384791297151545266869872279 577186945727317900304808419)
      ·
        refine ⟨865780418590976850457212629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577186945727317900304808419 865780418590976850457212629)
        ·
          refine ⟨20291728560726019932590921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 865780418590976850457212629 20291728560726019932590921)
          ·
            refine ⟨15218796420544514949443191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20291728560726019932590921 15218796420544514949443191)
            ·
              refine ⟨22828194630816772424164787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15218796420544514949443191 22828194630816772424164787)
              ·
                refine ⟨34242291946225158636247181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22828194630816772424164787 34242291946225158636247181)
                ·
                  refine ⟨12840859479834434488592693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34242291946225158636247181 12840859479834434488592693)
                  ·
                    refine ⟨1203830576234478233305565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12840859479834434488592693 1203830576234478233305565)
                    ·
                      rfl

theorem cell23_7033355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 5].length) (baseStart_7033355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033355 prefixEnd_7033355 := by exact prefixLift 7033355
  have htrace : WordTrace (prefixWord ++ tailWord_7033355) baseStart_7033355 baseEnd_7033355 := by
    simpa [prefixWord, tailWord_7033355, baseEnd_7033355] using wordTrace_append hprefix tailTrace_7033355
  have hstable : (prefixWord ++ tailWord_7033355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033355).length < 2 ^ (prefixWord ++ tailWord_7033355).sum := by decide
  have hdescent : baseEnd_7033355 < baseStart_7033355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033380 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_7033380 : Nat := 118140960795 + 7033380 * 2 ^ 59
def prefixEnd_7033380 : Nat := 4983230072969 + 3 ^ 40 * 7033380 * 2
def baseEnd_7033380 : Nat := 1203834855239932367368027

theorem tailTrace_7033380 : CollatzResearch.WordTrace tailWord_7033380 prefixEnd_7033380 1203834855239932367368027 := by
  unfold tailWord_7033380
  simp only [CollatzResearch.WordTrace]
  refine ⟨128264221629636470258120797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171018962172848627010827729 128264221629636470258120797)
  ·
    refine ⟨48099083111113676346795299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128264221629636470258120797 48099083111113676346795299)
    ·
      refine ⟨72148624666670514520192949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48099083111113676346795299 72148624666670514520192949)
      ·
        refine ⟨6763933562500360736268089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72148624666670514520192949 6763933562500360736268089)
        ·
          refine ⟨5072950171875270552201067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6763933562500360736268089 5072950171875270552201067)
          ·
            refine ⟨7609425257812905828301601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072950171875270552201067 7609425257812905828301601)
            ·
              refine ⟨5707068943359679371226201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609425257812905828301601 5707068943359679371226201)
              ·
                refine ⟨4280301707519759528419651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707068943359679371226201 4280301707519759528419651)
                ·
                  refine ⟨6420452561279639292629477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280301707519759528419651 6420452561279639292629477)
                  ·
                    refine ⟨1203834855239932367368027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420452561279639292629477 1203834855239932367368027)
                    ·
                      rfl

theorem cell23_7033380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_7033380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033380 prefixEnd_7033380 := by exact prefixLift 7033380
  have htrace : WordTrace (prefixWord ++ tailWord_7033380) baseStart_7033380 baseEnd_7033380 := by
    simpa [prefixWord, tailWord_7033380, baseEnd_7033380] using wordTrace_append hprefix tailTrace_7033380
  have hstable : (prefixWord ++ tailWord_7033380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033380).length < 2 ^ (prefixWord ++ tailWord_7033380).sum := by decide
  have hdescent : baseEnd_7033380 < baseStart_7033380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033386 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_7033386 : Nat := 118140960795 + 7033386 * 2 ^ 59
def prefixEnd_7033386 : Nat := 4983230072969 + 3 ^ 40 * 7033386 * 2
def baseEnd_7033386 : Nat := 3611507646603724078629053

theorem tailTrace_7033386 : CollatzResearch.WordTrace tailWord_7033386 prefixEnd_7033386 3611507646603724078629053 := by
  unfold tailWord_7033386
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132165524312800885240003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171019108064834135693973341 64132165524312800885240003)
  ·
    refine ⟨96198248286469201327860005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64132165524312800885240003 96198248286469201327860005)
    ·
      refine ⟨18037171553712975248973751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96198248286469201327860005 18037171553712975248973751)
      ·
        refine ⟨27055757330569462873460627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18037171553712975248973751 27055757330569462873460627)
        ·
          refine ⟨40583635995854194310190941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27055757330569462873460627 40583635995854194310190941)
          ·
            refine ⟨15218863498445322866321603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40583635995854194310190941 15218863498445322866321603)
            ·
              refine ⟨22828295247667984299482405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15218863498445322866321603 22828295247667984299482405)
              ·
                refine ⟨4280305358937747056152951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22828295247667984299482405 4280305358937747056152951)
                ·
                  refine ⟨6420458038406620584229427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280305358937747056152951 6420458038406620584229427)
                  ·
                    refine ⟨9630687057609930876344141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420458038406620584229427 9630687057609930876344141)
                    ·
                      refine ⟨3611507646603724078629053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630687057609930876344141 3611507646603724078629053)
                      ·
                        rfl

theorem cell23_7033386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_7033386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033386 prefixEnd_7033386 := by exact prefixLift 7033386
  have htrace : WordTrace (prefixWord ++ tailWord_7033386) baseStart_7033386 baseEnd_7033386 := by
    simpa [prefixWord, tailWord_7033386, baseEnd_7033386] using wordTrace_append hprefix tailTrace_7033386
  have hstable : (prefixWord ++ tailWord_7033386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033386).length < 2 ^ (prefixWord ++ tailWord_7033386).sum := by decide
  have hdescent : baseEnd_7033386 < baseStart_7033386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033388 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_7033388 : Nat := 118140960795 + 7033388 * 2 ^ 59
def prefixEnd_7033388 : Nat := 4983230072969 + 3 ^ 40 * 7033388 * 2
def baseEnd_7033388 : Nat := 3611508673565033070804043

theorem tailTrace_7033388 : CollatzResearch.WordTrace tailWord_7033388 prefixEnd_7033388 3611508673565033070804043 := by
  unfold tailWord_7033388
  simp only [CollatzResearch.WordTrace]
  refine ⟨128264367521621978941266409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171019156695495971921688545 128264367521621978941266409)
  ·
    refine ⟨96198275641216484205949807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128264367521621978941266409 96198275641216484205949807)
    ·
      refine ⟨144297413461824726308924711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96198275641216484205949807 144297413461824726308924711)
      ·
        refine ⟨216446120192737089463387067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144297413461824726308924711 216446120192737089463387067)
        ·
          refine ⟨324669180289105634195080601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216446120192737089463387067 324669180289105634195080601)
          ·
            refine ⟨243501885216829225646310451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324669180289105634195080601 243501885216829225646310451)
            ·
              refine ⟨365252827825243838469465677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243501885216829225646310451 365252827825243838469465677)
              ·
                refine ⟨136969810434466439426049629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365252827825243838469465677 136969810434466439426049629)
                ·
                  refine ⟨51363678912924914784768611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136969810434466439426049629 51363678912924914784768611)
                  ·
                    refine ⟨77045518369387372177152917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51363678912924914784768611 77045518369387372177152917)
                    ·
                      refine ⟨3611508673565033070804043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77045518369387372177152917 3611508673565033070804043)
                      ·
                        rfl

theorem cell23_7033388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_7033388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033388 prefixEnd_7033388 := by exact prefixLift 7033388
  have htrace : WordTrace (prefixWord ++ tailWord_7033388) baseStart_7033388 baseEnd_7033388 := by
    simpa [prefixWord, tailWord_7033388, baseEnd_7033388] using wordTrace_append hprefix tailTrace_7033388
  have hstable : (prefixWord ++ tailWord_7033388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033388).length < 2 ^ (prefixWord ++ tailWord_7033388).sum := by decide
  have hdescent : baseEnd_7033388 < baseStart_7033388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033395 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3]
def baseStart_7033395 : Nat := 118140960795 + 7033395 * 2 ^ 59
def prefixEnd_7033395 : Nat := 4983230072969 + 3 ^ 40 * 7033395 * 2
def baseEnd_7033395 : Nat := 3611512267929614543416511

theorem tailTrace_7033395 : CollatzResearch.WordTrace tailWord_7033395 prefixEnd_7033395 3611512267929614543416511 := by
  unfold tailWord_7033395
  simp only [CollatzResearch.WordTrace]
  refine ⟨256528990354218598078037639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171019326902812398718691759 256528990354218598078037639)
  ·
    refine ⟨384793485531327897117056459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256528990354218598078037639 384793485531327897117056459)
    ·
      refine ⟨577190228296991845675584689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384793485531327897117056459 577190228296991845675584689)
      ·
        refine ⟨432892671222743884256688517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577190228296991845675584689 432892671222743884256688517)
        ·
          refine ⟨81167375854264478298129097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432892671222743884256688517 81167375854264478298129097)
          ·
            refine ⟨60875531890698358723596823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81167375854264478298129097 60875531890698358723596823)
            ·
              refine ⟨91313297836047538085395235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60875531890698358723596823 91313297836047538085395235)
              ·
                refine ⟨136969946754071307128092853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91313297836047538085395235 136969946754071307128092853)
                ·
                  refine ⟨12840932508194185043258705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136969946754071307128092853 12840932508194185043258705)
                  ·
                    refine ⟨9630699381145638782444029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12840932508194185043258705 9630699381145638782444029)
                    ·
                      refine ⟨3611512267929614543416511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630699381145638782444029 3611512267929614543416511)
                      ·
                        rfl

theorem cell23_7033395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_7033395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033395 prefixEnd_7033395 := by exact prefixLift 7033395
  have htrace : WordTrace (prefixWord ++ tailWord_7033395) baseStart_7033395 baseEnd_7033395 := by
    simpa [prefixWord, tailWord_7033395, baseEnd_7033395] using wordTrace_append hprefix tailTrace_7033395
  have hstable : (prefixWord ++ tailWord_7033395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033395).length < 2 ^ (prefixWord ++ tailWord_7033395).sum := by decide
  have hdescent : baseEnd_7033395 < baseStart_7033395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033402 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_7033402 : Nat := 118140960795 + 7033402 * 2 ^ 59
def prefixEnd_7033402 : Nat := 4983230072969 + 3 ^ 40 * 7033402 * 2
def baseEnd_7033402 : Nat := 1203838620764732005342993

theorem tailTrace_7033402 : CollatzResearch.WordTrace tailWord_7033402 prefixEnd_7033402 1203838620764732005342993 := by
  unfold tailWord_7033402
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132311416298309568385615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171019497110128825515694973 64132311416298309568385615)
  ·
    refine ⟨96198467124447464352578423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64132311416298309568385615 96198467124447464352578423)
    ·
      refine ⟨144297700686671196528867635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96198467124447464352578423 144297700686671196528867635)
      ·
        refine ⟨216446551030006794793301453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144297700686671196528867635 216446551030006794793301453)
        ·
          refine ⟨81167456636252548047488045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216446551030006794793301453 81167456636252548047488045)
          ·
            refine ⟨30437796238594705517808017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81167456636252548047488045 30437796238594705517808017)
            ·
              refine ⟨22828347178946029138356013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30437796238594705517808017 22828347178946029138356013)
              ·
                refine ⟨8560630192104760926883505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22828347178946029138356013 8560630192104760926883505)
                ·
                  refine ⟨6420472644078570695162629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560630192104760926883505 6420472644078570695162629)
                  ·
                    refine ⟨1203838620764732005342993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420472644078570695162629 1203838620764732005342993)
                    ·
                      rfl

theorem cell23_7033402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_7033402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033402 prefixEnd_7033402 := by exact prefixLift 7033402
  have htrace : WordTrace (prefixWord ++ tailWord_7033402) baseStart_7033402 baseEnd_7033402 := by
    simpa [prefixWord, tailWord_7033402, baseEnd_7033402] using wordTrace_append hprefix tailTrace_7033402
  have hstable : (prefixWord ++ tailWord_7033402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033402).length < 2 ^ (prefixWord ++ tailWord_7033402).sum := by decide
  have hdescent : baseEnd_7033402 < baseStart_7033402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033409 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7033409 : Nat := 118140960795 + 7033409 * 2 ^ 59
def prefixEnd_7033409 : Nat := 4983230072969 + 3 ^ 40 * 7033409 * 2
def baseEnd_7033409 : Nat := 3611519456658777488641447

theorem tailTrace_7033409 : CollatzResearch.WordTrace tailWord_7033409 prefixEnd_7033409 3611519456658777488641447 := by
  unfold tailWord_7033409
  simp only [CollatzResearch.WordTrace]
  refine ⟨256529500976167878469047281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171019667317445252312698187 256529500976167878469047281)
  ·
    refine ⟨192397125732125908851785461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256529500976167878469047281 192397125732125908851785461)
    ·
      refine ⟨18037230537386803954854887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192397125732125908851785461 18037230537386803954854887)
      ·
        refine ⟨27055845806080205932282331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18037230537386803954854887 27055845806080205932282331)
        ·
          refine ⟨40583768709120308898423497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27055845806080205932282331 40583768709120308898423497)
          ·
            refine ⟨30437826531840231673817623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40583768709120308898423497 30437826531840231673817623)
            ·
              refine ⟨45656739797760347510726435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30437826531840231673817623 45656739797760347510726435)
              ·
                refine ⟨68485109696640521266089653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45656739797760347510726435 68485109696640521266089653)
                ·
                  refine ⟨6420479034060048868695905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68485109696640521266089653 6420479034060048868695905)
                  ·
                    refine ⟨4815359275545036651521929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420479034060048868695905 4815359275545036651521929)
                    ·
                      refine ⟨3611519456658777488641447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815359275545036651521929 3611519456658777488641447)
                      ·
                        rfl

theorem cell23_7033409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7033409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033409 prefixEnd_7033409 := by exact prefixLift 7033409
  have htrace : WordTrace (prefixWord ++ tailWord_7033409) baseStart_7033409 baseEnd_7033409 := by
    simpa [prefixWord, tailWord_7033409, baseEnd_7033409] using wordTrace_append hprefix tailTrace_7033409
  have hstable : (prefixWord ++ tailWord_7033409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033409).length < 2 ^ (prefixWord ++ tailWord_7033409).sum := by decide
  have hdescent : baseEnd_7033409 < baseStart_7033409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033429 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_7033429 : Nat := 118140960795 + 7033429 * 2 ^ 59
def prefixEnd_7033429 : Nat := 4983230072969 + 3 ^ 40 * 7033429 * 2
def baseEnd_7033429 : Nat := 3611529726271867410391355

theorem tailTrace_7033429 : CollatzResearch.WordTrace tailWord_7033429 prefixEnd_7033429 3611529726271867410391355 := by
  unfold tailWord_7033429
  simp only [CollatzResearch.WordTrace]
  refine ⟨256530230436095421884775341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171020153624063614589850227 256530230436095421884775341)
  ·
    refine ⟨96198836413535783206790753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256530230436095421884775341 96198836413535783206790753)
    ·
      refine ⟨72149127310151837405093065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96198836413535783206790753 72149127310151837405093065)
      ·
        refine ⟨54111845482613878053819799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72149127310151837405093065 54111845482613878053819799)
        ·
          refine ⟨81167768223920817080729699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54111845482613878053819799 81167768223920817080729699)
          ·
            refine ⟨121751652335881225621094549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81167768223920817080729699 121751652335881225621094549)
            ·
              refine ⟨5707108703244432450988807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121751652335881225621094549 5707108703244432450988807)
              ·
                refine ⟨8560663054866648676483211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707108703244432450988807 8560663054866648676483211)
                ·
                  refine ⟨12840994582299973014724817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560663054866648676483211 12840994582299973014724817)
                  ·
                    refine ⟨9630745936724979761043613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12840994582299973014724817 9630745936724979761043613)
                    ·
                      refine ⟨3611529726271867410391355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630745936724979761043613 3611529726271867410391355)
                      ·
                        rfl

theorem cell23_7033429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_7033429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033429 prefixEnd_7033429 := by exact prefixLift 7033429
  have htrace : WordTrace (prefixWord ++ tailWord_7033429) baseStart_7033429 baseEnd_7033429 := by
    simpa [prefixWord, tailWord_7033429, baseEnd_7033429] using wordTrace_append hprefix tailTrace_7033429
  have hstable : (prefixWord ++ tailWord_7033429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033429).length < 2 ^ (prefixWord ++ tailWord_7033429).sum := by decide
  have hdescent : baseEnd_7033429 < baseStart_7033429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033436 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_7033436 : Nat := 118140960795 + 7033436 * 2 ^ 59
def prefixEnd_7033436 : Nat := 4983230072969 + 3 ^ 40 * 7033436 * 2
def baseEnd_7033436 : Nat := 1203844440212149627667941

theorem tailTrace_7033436 : CollatzResearch.WordTrace tailWord_7033436 prefixEnd_7033436 1203844440212149627667941 := by
  unfold tailWord_7033436
  simp only [CollatzResearch.WordTrace]
  refine ⟨128265242873535031040140081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171020323831380041386853441 128265242873535031040140081)
  ·
    refine ⟨96198932155151273280105061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128265242873535031040140081 96198932155151273280105061)
    ·
      refine ⟨18037299779090863740019699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96198932155151273280105061 18037299779090863740019699)
      ·
        refine ⟨27055949668636295610029549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18037299779090863740019699 27055949668636295610029549)
        ·
          refine ⟨10145981125738610853761081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27055949668636295610029549 10145981125738610853761081)
          ·
            refine ⟨7609485844303958140320811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10145981125738610853761081 7609485844303958140320811)
            ·
              refine ⟨11414228766455937210481217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609485844303958140320811 11414228766455937210481217)
              ·
                refine ⟨8560671574841952907860913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11414228766455937210481217 8560671574841952907860913)
                ·
                  refine ⟨6420503681131464680895685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560671574841952907860913 6420503681131464680895685)
                  ·
                    refine ⟨1203844440212149627667941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420503681131464680895685 1203844440212149627667941)
                    ·
                      rfl

theorem cell23_7033436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_7033436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033436 prefixEnd_7033436 := by exact prefixLift 7033436
  have htrace : WordTrace (prefixWord ++ tailWord_7033436) baseStart_7033436 baseEnd_7033436 := by
    simpa [prefixWord, tailWord_7033436, baseEnd_7033436] using wordTrace_append hprefix tailTrace_7033436
  have hstable : (prefixWord ++ tailWord_7033436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033436).length < 2 ^ (prefixWord ++ tailWord_7033436).sum := by decide
  have hdescent : baseEnd_7033436 < baseStart_7033436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033452 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_7033452 : Nat := 118140960795 + 7033452 * 2 ^ 59
def prefixEnd_7033452 : Nat := 4983230072969 + 3 ^ 40 * 7033452 * 2
def baseEnd_7033452 : Nat := 3611541536326920820403749

theorem tailTrace_7033452 : CollatzResearch.WordTrace tailWord_7033452 prefixEnd_7033452 3611541536326920820403749 := by
  unfold tailWord_7033452
  simp only [CollatzResearch.WordTrace]
  refine ⟨128265534657506048406431305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171020712876674731208575073 128265534657506048406431305)
  ·
    refine ⟨96199150993129536304823479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128265534657506048406431305 96199150993129536304823479)
    ·
      refine ⟨144298726489694304457235219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96199150993129536304823479 144298726489694304457235219)
      ·
        refine ⟨216448089734541456685852829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144298726489694304457235219 216448089734541456685852829)
        ·
          refine ⟨81168033650453046257194811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216448089734541456685852829 81168033650453046257194811)
          ·
            refine ⟨121752050475679569385792217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81168033650453046257194811 121752050475679569385792217)
            ·
              refine ⟨91314037856759677039344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121752050475679569385792217 91314037856759677039344163)
              ·
                refine ⟨136971056785139515559016245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91314037856759677039344163 136971056785139515559016245)
                ·
                  refine ⟨12841036573606829583657773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136971056785139515559016245 12841036573606829583657773)
                  ·
                    refine ⟨4815388715102561093871665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12841036573606829583657773 4815388715102561093871665)
                    ·
                      refine ⟨3611541536326920820403749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815388715102561093871665 3611541536326920820403749)
                      ·
                        rfl

theorem cell23_7033452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_7033452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033452 prefixEnd_7033452 := by exact prefixLift 7033452
  have htrace : WordTrace (prefixWord ++ tailWord_7033452) baseStart_7033452 baseEnd_7033452 := by
    simpa [prefixWord, tailWord_7033452, baseEnd_7033452] using wordTrace_append hprefix tailTrace_7033452
  have hstable : (prefixWord ++ tailWord_7033452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033452).length < 2 ^ (prefixWord ++ tailWord_7033452).sum := by decide
  have hdescent : baseEnd_7033452 < baseStart_7033452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033502 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7033502 : Nat := 118140960795 + 7033502 * 2 ^ 59
def prefixEnd_7033502 : Nat := 4983230072969 + 3 ^ 40 * 7033502 * 2
def baseEnd_7033502 : Nat := 3611567210359645624778519

theorem tailTrace_7033502 : CollatzResearch.WordTrace tailWord_7033502 prefixEnd_7033502 3611567210359645624778519 := by
  unfold tailWord_7033502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066611620603869419022845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171021928643220636901455173 32066611620603869419022845)
  ·
    refine ⟨12024979357726451032133567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32066611620603869419022845 12024979357726451032133567)
    ·
      refine ⟨18037469036589676548200351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12024979357726451032133567 18037469036589676548200351)
      ·
        refine ⟨27056203554884514822300527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18037469036589676548200351 27056203554884514822300527)
        ·
          refine ⟨40584305332326772233450791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27056203554884514822300527 40584305332326772233450791)
          ·
            refine ⟨60876457998490158350176187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40584305332326772233450791 60876457998490158350176187)
            ·
              refine ⟨91314686997735237525264281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60876457998490158350176187 91314686997735237525264281)
              ·
                refine ⟨68486015248301428143948211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91314686997735237525264281 68486015248301428143948211)
                ·
                  refine ⟨102729022872452142215922317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68486015248301428143948211 102729022872452142215922317)
                  ·
                    refine ⟨38523383577169553330970869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102729022872452142215922317 38523383577169553330970869)
                    ·
                      refine ⟨3611567210359645624778519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38523383577169553330970869 3611567210359645624778519)
                      ·
                        rfl

theorem cell23_7033502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7033502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033502 prefixEnd_7033502 := by exact prefixLift 7033502
  have htrace : WordTrace (prefixWord ++ tailWord_7033502) baseStart_7033502 baseEnd_7033502 := by
    simpa [prefixWord, tailWord_7033502, baseEnd_7033502] using wordTrace_append hprefix tailTrace_7033502
  have hstable : (prefixWord ++ tailWord_7033502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033502).length < 2 ^ (prefixWord ++ tailWord_7033502).sum := by decide
  have hdescent : baseEnd_7033502 < baseStart_7033502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033556 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 5]
def baseStart_7033556 : Nat := 118140960795 + 7033556 * 2 ^ 59
def prefixEnd_7033556 : Nat := 4983230072969 + 3 ^ 40 * 7033556 * 2
def baseEnd_7033556 : Nat := 401288326479443157055919

theorem tailTrace_7033556 : CollatzResearch.WordTrace tailWord_7033556 prefixEnd_7033556 401288326479443157055919 := by
  unfold tailWord_7033556
  simp only [CollatzResearch.WordTrace]
  refine ⟨128267431253317661287324261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171023241671090215049765681 128267431253317661287324261)
  ·
    refine ⟨24050143359997061491373299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128267431253317661287324261 24050143359997061491373299)
    ·
      refine ⟨36075215039995592237059949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24050143359997061491373299 36075215039995592237059949)
      ·
        refine ⟨13528205639998347088897481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36075215039995592237059949 13528205639998347088897481)
        ·
          refine ⟨10146154229998760316673111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13528205639998347088897481 10146154229998760316673111)
          ·
            refine ⟨15219231344998140475009667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10146154229998760316673111 15219231344998140475009667)
            ·
              refine ⟨22828847017497210712514501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15219231344998140475009667 22828847017497210712514501)
              ·
                refine ⟨4280408815780727008596469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22828847017497210712514501 4280408815780727008596469)
                ·
                  refine ⟨401288326479443157055919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4280408815780727008596469 401288326479443157055919)
                  ·
                    rfl

theorem cell23_7033556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_7033556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033556 prefixEnd_7033556 := by exact prefixLift 7033556
  have htrace : WordTrace (prefixWord ++ tailWord_7033556) baseStart_7033556 baseEnd_7033556 := by
    simpa [prefixWord, tailWord_7033556, baseEnd_7033556] using wordTrace_append hprefix tailTrace_7033556
  have hstable : (prefixWord ++ tailWord_7033556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033556).length < 2 ^ (prefixWord ++ tailWord_7033556).sum := by decide
  have hdescent : baseEnd_7033556 < baseStart_7033556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033592 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_7033592 : Nat := 118140960795 + 7033592 * 2 ^ 59
def prefixEnd_7033592 : Nat := 4983230072969 + 3 ^ 40 * 7033592 * 2
def baseEnd_7033592 : Nat := 3611613423618550272653105

theorem tailTrace_7033592 : CollatzResearch.WordTrace tailWord_7033592 prefixEnd_7033592 3611613423618550272653105 := by
  unfold tailWord_7033592
  simp only [CollatzResearch.WordTrace]
  refine ⟨128268087767252450361479515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171024117023003267148639353 128268087767252450361479515)
  ·
    refine ⟨192402131650878675542219273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128268087767252450361479515 192402131650878675542219273)
    ·
      refine ⟨144301598738159006656664455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192402131650878675542219273 144301598738159006656664455)
      ·
        refine ⟨216452398107238509984996683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144301598738159006656664455 216452398107238509984996683)
        ·
          refine ⟨324678597160857764977495025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216452398107238509984996683 324678597160857764977495025)
          ·
            refine ⟨243508947870643323733121269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324678597160857764977495025 243508947870643323733121269)
            ·
              refine ⟨22828963862872811599980119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243508947870643323733121269 22828963862872811599980119)
              ·
                refine ⟨34243445794309217399970179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22828963862872811599980119 34243445794309217399970179)
                ·
                  refine ⟨51365168691463826099955269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34243445794309217399970179 51365168691463826099955269)
                  ·
                    refine ⟨9630969129649467393741613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51365168691463826099955269 9630969129649467393741613)
                    ·
                      refine ⟨3611613423618550272653105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9630969129649467393741613 3611613423618550272653105)
                      ·
                        rfl

theorem cell23_7033592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_7033592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033592 prefixEnd_7033592 := by exact prefixLift 7033592
  have htrace : WordTrace (prefixWord ++ tailWord_7033592) baseStart_7033592 baseEnd_7033592 := by
    simpa [prefixWord, tailWord_7033592, baseEnd_7033592] using wordTrace_append hprefix tailTrace_7033592
  have hstable : (prefixWord ++ tailWord_7033592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033592).length < 2 ^ (prefixWord ++ tailWord_7033592).sum := by decide
  have hdescent : baseEnd_7033592 < baseStart_7033592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033615 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_7033615 : Nat := 118140960795 + 7033615 * 2 ^ 59
def prefixEnd_7033615 : Nat := 4983230072969 + 3 ^ 40 * 7033615 * 2
def baseEnd_7033615 : Nat := 3611625233673603682665499

theorem tailTrace_7033615 : CollatzResearch.WordTrace tailWord_7033615 prefixEnd_7033615 3611625233673603682665499 := by
  unfold tailWord_7033615
  simp only [CollatzResearch.WordTrace]
  refine ⟨256537014413421575651046299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171024676275614383767364199 256537014413421575651046299)
  ·
    refine ⟨384805521620132363476569449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256537014413421575651046299 384805521620132363476569449)
    ·
      refine ⟨288604141215099272607427087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384805521620132363476569449 288604141215099272607427087)
      ·
        refine ⟨432906211822648908911140631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288604141215099272607427087 432906211822648908911140631)
        ·
          refine ⟨649359317733973363366710947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432906211822648908911140631 649359317733973363366710947)
          ·
            refine ⟨974038976600960045050066421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649359317733973363366710947 974038976600960045050066421)
            ·
              refine ⟨91316154056340004223443727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 974038976600960045050066421 91316154056340004223443727)
              ·
                refine ⟨136974231084510006335165591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91316154056340004223443727 136974231084510006335165591)
                ·
                  refine ⟨205461346626765009502748387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136974231084510006335165591 205461346626765009502748387)
                  ·
                    refine ⟨308192019940147514254122581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205461346626765009502748387 308192019940147514254122581)
                    ·
                      refine ⟨3611625233673603682665499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 308192019940147514254122581 3611625233673603682665499)
                      ·
                        rfl

theorem cell23_7033615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_7033615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033615 prefixEnd_7033615 := by exact prefixLift 7033615
  have htrace : WordTrace (prefixWord ++ tailWord_7033615) baseStart_7033615 baseEnd_7033615 := by
    simpa [prefixWord, tailWord_7033615, baseEnd_7033615] using wordTrace_append hprefix tailTrace_7033615
  have hstable : (prefixWord ++ tailWord_7033615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033615).length < 2 ^ (prefixWord ++ tailWord_7033615).sum := by decide
  have hdescent : baseEnd_7033615 < baseStart_7033615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033625 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_7033625 : Nat := 118140960795 + 7033625 * 2 ^ 59
def prefixEnd_7033625 : Nat := 4983230072969 + 3 ^ 40 * 7033625 * 2
def baseEnd_7033625 : Nat := 1203876789493382881180151

theorem tailTrace_7033625 : CollatzResearch.WordTrace tailWord_7033625 prefixEnd_7033625 1203876789493382881180151 := by
  unfold tailWord_7033625
  simp only [CollatzResearch.WordTrace]
  refine ⟨256537379143385347358910329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171024919428923564905940219 256537379143385347358910329)
  ·
    refine ⟨192403034357539010519182747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256537379143385347358910329 192403034357539010519182747)
    ·
      refine ⟨288604551536308515778774121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192403034357539010519182747 288604551536308515778774121)
      ·
        refine ⟨216453413652231386834080591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288604551536308515778774121 216453413652231386834080591)
        ·
          refine ⟨324680120478347080251120887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216453413652231386834080591 324680120478347080251120887)
          ·
            refine ⟨487020180717520620376681331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324680120478347080251120887 487020180717520620376681331)
            ·
              refine ⟨730530271076280930565021997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487020180717520620376681331 730530271076280930565021997)
              ·
                refine ⟨273948851653605348961883249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 730530271076280930565021997 273948851653605348961883249)
                ·
                  refine ⟨205461638740204011721412437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273948851653605348961883249 205461638740204011721412437)
                  ·
                    refine ⟨1203876789493382881180151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205461638740204011721412437 1203876789493382881180151)
                    ·
                      rfl

theorem cell23_7033625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_7033625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033625 prefixEnd_7033625 := by exact prefixLift 7033625
  have htrace : WordTrace (prefixWord ++ tailWord_7033625) baseStart_7033625 baseEnd_7033625 := by
    simpa [prefixWord, tailWord_7033625, baseEnd_7033625] using wordTrace_append hprefix tailTrace_7033625
  have hstable : (prefixWord ++ tailWord_7033625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033625).length < 2 ^ (prefixWord ++ tailWord_7033625).sum := by decide
  have hdescent : baseEnd_7033625 < baseStart_7033625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033649 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_7033649 : Nat := 118140960795 + 7033649 * 2 ^ 59
def prefixEnd_7033649 : Nat := 4983230072969 + 3 ^ 40 * 7033649 * 2
def baseEnd_7033649 : Nat := 3611642692015856549640343

theorem tailTrace_7033649 : CollatzResearch.WordTrace tailWord_7033649 prefixEnd_7033649 3611642692015856549640343 := by
  unfold tailWord_7033649
  simp only [CollatzResearch.WordTrace]
  refine ⟨256538254495298399457784001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171025502996865599638522667 256538254495298399457784001)
  ·
    refine ⟨192403690871473799593338001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256538254495298399457784001 192403690871473799593338001)
    ·
      refine ⟨144302768153605349695003501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192403690871473799593338001 144302768153605349695003501)
      ·
        refine ⟨54113538057602006135626313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144302768153605349695003501 54113538057602006135626313)
        ·
          refine ⟨40585153543201504601719735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54113538057602006135626313 40585153543201504601719735)
          ·
            refine ⟨60877730314802256902579603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40585153543201504601719735 60877730314802256902579603)
            ·
              refine ⟨91316595472203385353869405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60877730314802256902579603 91316595472203385353869405)
              ·
                refine ⟨34243723302076269507701027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91316595472203385353869405 34243723302076269507701027)
                ·
                  refine ⟨51365584953114404261551541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34243723302076269507701027 51365584953114404261551541)
                  ·
                    refine ⟨4815523589354475399520457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51365584953114404261551541 4815523589354475399520457)
                    ·
                      refine ⟨3611642692015856549640343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815523589354475399520457 3611642692015856549640343)
                      ·
                        rfl

theorem cell23_7033649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_7033649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033649 prefixEnd_7033649 := by exact prefixLift 7033649
  have htrace : WordTrace (prefixWord ++ tailWord_7033649) baseStart_7033649 baseEnd_7033649 := by
    simpa [prefixWord, tailWord_7033649, baseEnd_7033649] using wordTrace_append hprefix tailTrace_7033649
  have hstable : (prefixWord ++ tailWord_7033649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033649).length < 2 ^ (prefixWord ++ tailWord_7033649).sum := by decide
  have hdescent : baseEnd_7033649 < baseStart_7033649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033696 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2]
def baseStart_7033696 : Nat := 118140960795 + 7033696 * 2 ^ 59
def prefixEnd_7033696 : Nat := 4983230072969 + 3 ^ 40 * 7033696 * 2
def baseEnd_7033696 : Nat := 3611666825606617865752627

theorem tailTrace_7033696 : CollatzResearch.WordTrace tailWord_7033696 prefixEnd_7033696 3611666825606617865752627 := by
  unfold tailWord_7033696
  simp only [CollatzResearch.WordTrace]
  refine ⟨128269984363064063242372471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171026645817418750989829961 128269984363064063242372471)
  ·
    refine ⟨192404976544596094863558707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128269984363064063242372471 192404976544596094863558707)
    ·
      refine ⟨288607464816894142295338061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192404976544596094863558707 288607464816894142295338061)
      ·
        refine ⟨108227799306335303360751773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288607464816894142295338061 108227799306335303360751773)
        ·
          refine ⟨40585424739875738760281915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108227799306335303360751773 40585424739875738760281915)
          ·
            refine ⟨60878137109813608140422873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40585424739875738760281915 60878137109813608140422873)
            ·
              refine ⟨45658602832360206105317155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60878137109813608140422873 45658602832360206105317155)
              ·
                refine ⟨68487904248540309157975733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45658602832360206105317155 68487904248540309157975733)
                ·
                  refine ⟨6420741023300653983560225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68487904248540309157975733 6420741023300653983560225)
                  ·
                    refine ⟨4815555767475490487670169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6420741023300653983560225 4815555767475490487670169)
                    ·
                      refine ⟨3611666825606617865752627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815555767475490487670169 3611666825606617865752627)
                      ·
                        rfl

theorem cell23_7033696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_7033696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033696 prefixEnd_7033696 := by exact prefixLift 7033696
  have htrace : WordTrace (prefixWord ++ tailWord_7033696) baseStart_7033696 baseEnd_7033696 := by
    simpa [prefixWord, tailWord_7033696, baseEnd_7033696] using wordTrace_append hprefix tailTrace_7033696
  have hstable : (prefixWord ++ tailWord_7033696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033696).length < 2 ^ (prefixWord ++ tailWord_7033696).sum := by decide
  have hdescent : baseEnd_7033696 < baseStart_7033696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033750 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7033750 : Nat := 118140960795 + 7033750 * 2 ^ 59
def prefixEnd_7033750 : Nat := 4983230072969 + 3 ^ 40 * 7033750 * 2
def baseEnd_7033750 : Nat := 3611694553561960654477379

theorem tailTrace_7033750 : CollatzResearch.WordTrace tailWord_7033750 prefixEnd_7033750 3611694553561960654477379 := by
  unfold tailWord_7033750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033871141745780856700669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171027958845288329138140469 16033871141745780856700669)
  ·
    refine ⟨6012701678154667821262751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16033871141745780856700669 6012701678154667821262751)
    ·
      refine ⟨9019052517232001731894127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012701678154667821262751 9019052517232001731894127)
      ·
        refine ⟨13528578775848002597841191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019052517232001731894127 13528578775848002597841191)
        ·
          refine ⟨20292868163772003896761787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528578775848002597841191 20292868163772003896761787)
          ·
            refine ⟨30439302245658005845142681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20292868163772003896761787 30439302245658005845142681)
            ·
              refine ⟨22829476684243504383857011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30439302245658005845142681 22829476684243504383857011)
              ·
                refine ⟨34244215026365256575785517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22829476684243504383857011 34244215026365256575785517)
                ·
                  refine ⟨12841580634886971215919569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34244215026365256575785517 12841580634886971215919569)
                  ·
                    refine ⟨9631185476165228411939677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12841580634886971215919569 9631185476165228411939677)
                    ·
                      refine ⟨3611694553561960654477379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631185476165228411939677 3611694553561960654477379)
                      ·
                        rfl

theorem cell23_7033750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7033750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033750 prefixEnd_7033750 := by exact prefixLift 7033750
  have htrace : WordTrace (prefixWord ++ tailWord_7033750) baseStart_7033750 baseEnd_7033750 := by
    simpa [prefixWord, tailWord_7033750, baseEnd_7033750] using wordTrace_append hprefix tailTrace_7033750
  have hstable : (prefixWord ++ tailWord_7033750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033750).length < 2 ^ (prefixWord ++ tailWord_7033750).sum := by decide
  have hdescent : baseEnd_7033750 < baseStart_7033750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033767 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_7033767 : Nat := 118140960795 + 7033767 * 2 ^ 59
def prefixEnd_7033767 : Nat := 4983230072969 + 3 ^ 40 * 7033767 * 2
def baseEnd_7033767 : Nat := 3611703282733087087964801

theorem tailTrace_7033767 : CollatzResearch.WordTrace tailWord_7033767 prefixEnd_7033767 3611703282733087087964801 := by
  unfold tailWord_7033767
  simp only [CollatzResearch.WordTrace]
  refine ⟨256542558308870905610579555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171028372205913937073719703 256542558308870905610579555)
  ·
    refine ⟨384813837463306358415869333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256542558308870905610579555 384813837463306358415869333)
    ·
      refine ⟨18038148631092485550743875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 384813837463306358415869333 18038148631092485550743875)
      ·
        refine ⟨27057222946638728326115813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18038148631092485550743875 27057222946638728326115813)
        ·
          refine ⟨5073229302494761561146715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27057222946638728326115813 5073229302494761561146715)
          ·
            refine ⟨7609843953742142341720073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073229302494761561146715 7609843953742142341720073)
            ·
              refine ⟨5707382965306606756290055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609843953742142341720073 5707382965306606756290055)
              ·
                refine ⟨8561074447959910134435083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707382965306606756290055 8561074447959910134435083)
                ·
                  refine ⟨12841611671939865201652625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8561074447959910134435083 12841611671939865201652625)
                  ·
                    refine ⟨9631208753954898901239469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12841611671939865201652625 9631208753954898901239469)
                    ·
                      refine ⟨3611703282733087087964801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631208753954898901239469 3611703282733087087964801)
                      ·
                        rfl

theorem cell23_7033767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_7033767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033767 prefixEnd_7033767 := by exact prefixLift 7033767
  have htrace : WordTrace (prefixWord ++ tailWord_7033767) baseStart_7033767 baseEnd_7033767 := by
    simpa [prefixWord, tailWord_7033767, baseEnd_7033767] using wordTrace_append hprefix tailTrace_7033767
  have hstable : (prefixWord ++ tailWord_7033767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033767).length < 2 ^ (prefixWord ++ tailWord_7033767).sum := by decide
  have hdescent : baseEnd_7033767 < baseStart_7033767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033780 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7033780 : Nat := 118140960795 + 7033780 * 2 ^ 59
def prefixEnd_7033780 : Nat := 4983230072969 + 3 ^ 40 * 7033780 * 2
def baseEnd_7033780 : Nat := 3611709957981595537102241

theorem tailTrace_7033780 : CollatzResearch.WordTrace tailWord_7033780 prefixEnd_7033780 3611709957981595537102241 := by
  unfold tailWord_7033780
  simp only [CollatzResearch.WordTrace]
  refine ⟨128271516228911904415401397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171028688305215872553868529 128271516228911904415401397)
  ·
    refine ⟨12025454646460491038943881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128271516228911904415401397 12025454646460491038943881)
    ·
      refine ⟨9019090984845368279207911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12025454646460491038943881 9019090984845368279207911)
      ·
        refine ⟨13528636477268052418811867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019090984845368279207911 13528636477268052418811867)
        ·
          refine ⟨20292954715902078628217801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528636477268052418811867 20292954715902078628217801)
          ·
            refine ⟨15219716036926558971163351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20292954715902078628217801 15219716036926558971163351)
            ·
              refine ⟨22829574055389838456745027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15219716036926558971163351 22829574055389838456745027)
              ·
                refine ⟨34244361083084757685117541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22829574055389838456745027 34244361083084757685117541)
                ·
                  refine ⟨6420817703078392065959539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34244361083084757685117541 6420817703078392065959539)
                  ·
                    refine ⟨9631226554617588098939309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420817703078392065959539 9631226554617588098939309)
                    ·
                      refine ⟨3611709957981595537102241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631226554617588098939309 3611709957981595537102241)
                      ·
                        rfl

theorem cell23_7033780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7033780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033780 prefixEnd_7033780 := by exact prefixLift 7033780
  have htrace : WordTrace (prefixWord ++ tailWord_7033780) baseStart_7033780 baseEnd_7033780 := by
    simpa [prefixWord, tailWord_7033780, baseEnd_7033780] using wordTrace_append hprefix tailTrace_7033780
  have hstable : (prefixWord ++ tailWord_7033780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033780).length < 2 ^ (prefixWord ++ tailWord_7033780).sum := by decide
  have hdescent : baseEnd_7033780 < baseStart_7033780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033799 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_7033799 : Nat := 118140960795 + 7033799 * 2 ^ 59
def prefixEnd_7033799 : Nat := 4983230072969 + 3 ^ 40 * 7033799 * 2
def baseEnd_7033799 : Nat := 3611719714114030962764653

theorem tailTrace_7033799 : CollatzResearch.WordTrace tailWord_7033799 prefixEnd_7033799 3611719714114030962764653 := by
  unfold tailWord_7033799
  simp only [CollatzResearch.WordTrace]
  refine ⟨256543725444754975075744451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171029150296503316717162967 256543725444754975075744451)
  ·
    refine ⟨384815588167132462613616677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256543725444754975075744451 384815588167132462613616677)
    ·
      refine ⟨72152922781337336740053127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384815588167132462613616677 72152922781337336740053127)
      ·
        refine ⟨108229384172006005110079691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72152922781337336740053127 108229384172006005110079691)
        ·
          refine ⟨162344076258009007665119537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108229384172006005110079691 162344076258009007665119537)
          ·
            refine ⟨121758057193506755748839653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162344076258009007665119537 121758057193506755748839653)
            ·
              refine ⟨22829635723782516702907435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121758057193506755748839653 22829635723782516702907435)
              ·
                refine ⟨34244453585673775054361153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22829635723782516702907435 34244453585673775054361153)
                ·
                  refine ⟨25683340189255331290770865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34244453585673775054361153 25683340189255331290770865)
                  ·
                    refine ⟨19262505141941498468078149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25683340189255331290770865 19262505141941498468078149)
                    ·
                      refine ⟨3611719714114030962764653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19262505141941498468078149 3611719714114030962764653)
                      ·
                        rfl

theorem cell23_7033799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_7033799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033799 prefixEnd_7033799 := by exact prefixLift 7033799
  have htrace : WordTrace (prefixWord ++ tailWord_7033799) baseStart_7033799 baseEnd_7033799 := by
    simpa [prefixWord, tailWord_7033799, baseEnd_7033799] using wordTrace_append hprefix tailTrace_7033799
  have hstable : (prefixWord ++ tailWord_7033799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033799).length < 2 ^ (prefixWord ++ tailWord_7033799).sum := by decide
  have hdescent : baseEnd_7033799 < baseStart_7033799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033803 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 1, 4, 2]
def baseStart_7033803 : Nat := 118140960795 + 7033803 * 2 ^ 59
def prefixEnd_7033803 : Nat := 4983230072969 + 3 ^ 40 * 7033803 * 2
def baseEnd_7033803 : Nat := 3611721768036648947114635

theorem tailTrace_7033803 : CollatzResearch.WordTrace tailWord_7033803 prefixEnd_7033803 3611721768036648947114635 := by
  unfold tailWord_7033803
  simp only [CollatzResearch.WordTrace]
  refine ⟨256543871336740483758890063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171029247557826989172593375 256543871336740483758890063)
  ·
    refine ⟨384815807005110725638335095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256543871336740483758890063 384815807005110725638335095)
    ·
      refine ⟨577223710507666088457502643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384815807005110725638335095 577223710507666088457502643)
      ·
        refine ⟨865835565761499132686253965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577223710507666088457502643 865835565761499132686253965)
        ·
          refine ⟨324688337160562174757345237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865835565761499132686253965 324688337160562174757345237)
          ·
            refine ⟨7609882902200675970875279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 324688337160562174757345237 7609882902200675970875279)
            ·
              refine ⟨11414824353301013956312919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609882902200675970875279 11414824353301013956312919)
              ·
                refine ⟨17122236529951520934469379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11414824353301013956312919 17122236529951520934469379)
                ·
                  refine ⟨25683354794927281401704069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17122236529951520934469379 25683354794927281401704069)
                  ·
                    refine ⟨4815629024048865262819513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25683354794927281401704069 4815629024048865262819513)
                    ·
                      refine ⟨3611721768036648947114635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815629024048865262819513 3611721768036648947114635)
                      ·
                        rfl

theorem cell23_7033803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4, 2].length) (baseStart_7033803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033803 prefixEnd_7033803 := by exact prefixLift 7033803
  have htrace : WordTrace (prefixWord ++ tailWord_7033803) baseStart_7033803 baseEnd_7033803 := by
    simpa [prefixWord, tailWord_7033803, baseEnd_7033803] using wordTrace_append hprefix tailTrace_7033803
  have hstable : (prefixWord ++ tailWord_7033803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033803).length < 2 ^ (prefixWord ++ tailWord_7033803).sum := by decide
  have hdescent : baseEnd_7033803 < baseStart_7033803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033839 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 4, 5]
def baseStart_7033839 : Nat := 118140960795 + 7033839 * 2 ^ 59
def prefixEnd_7033839 : Nat := 4983230072969 + 3 ^ 40 * 7033839 * 2
def baseEnd_7033839 : Nat := 1203913417780070268754823

theorem tailTrace_7033839 : CollatzResearch.WordTrace tailWord_7033839 prefixEnd_7033839 1203913417780070268754823 := by
  unfold tailWord_7033839
  simp only [CollatzResearch.WordTrace]
  refine ⟨256545184364610061907200571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171030122909740041271467047 256545184364610061907200571)
  ·
    refine ⟨384817776546915092860800857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256545184364610061907200571 384817776546915092860800857)
    ·
      refine ⟨288613332410186319645600643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384817776546915092860800857 288613332410186319645600643)
      ·
        refine ⟨432919998615279479468400965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288613332410186319645600643 432919998615279479468400965)
        ·
          refine ⟨81172499740364902400325181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432919998615279479468400965 81172499740364902400325181)
          ·
            refine ⟨30439687402636838400121943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81172499740364902400325181 30439687402636838400121943)
            ·
              refine ⟨45659531103955257600182915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30439687402636838400121943 45659531103955257600182915)
              ·
                refine ⟨68489296655932886400274373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45659531103955257600182915 68489296655932886400274373)
                ·
                  refine ⟨12841743122987416200051445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68489296655932886400274373 12841743122987416200051445)
                  ·
                    refine ⟨1203913417780070268754823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12841743122987416200051445 1203913417780070268754823)
                    ·
                      rfl

theorem cell23_7033839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_7033839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033839 prefixEnd_7033839 := by exact prefixLift 7033839
  have htrace : WordTrace (prefixWord ++ tailWord_7033839) baseStart_7033839 baseEnd_7033839 := by
    simpa [prefixWord, tailWord_7033839, baseEnd_7033839] using wordTrace_append hprefix tailTrace_7033839
  have hstable : (prefixWord ++ tailWord_7033839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033839).length < 2 ^ (prefixWord ++ tailWord_7033839).sum := by decide
  have hdescent : baseEnd_7033839 < baseStart_7033839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033849 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_7033849 : Nat := 118140960795 + 7033849 * 2 ^ 59
def prefixEnd_7033849 : Nat := 4983230072969 + 3 ^ 40 * 7033849 * 2
def baseEnd_7033849 : Nat := 3611745388146755767139423

theorem tailTrace_7033849 : CollatzResearch.WordTrace tailWord_7033849 prefixEnd_7033849 3611745388146755767139423 := by
  unfold tailWord_7033849
  simp only [CollatzResearch.WordTrace]
  refine ⟨256545549094573833615064601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171030366063049222410043067 256545549094573833615064601)
  ·
    refine ⟨192409161820930375211298451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256545549094573833615064601 192409161820930375211298451)
    ·
      refine ⟨288613742731395562816947677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192409161820930375211298451 288613742731395562816947677)
      ·
        refine ⟨108230153524273336056355379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288613742731395562816947677 108230153524273336056355379)
        ·
          refine ⟨162345230286410004084533069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108230153524273336056355379 162345230286410004084533069)
          ·
            refine ⟨60879461357403751531699901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162345230286410004084533069 60879461357403751531699901)
            ·
              refine ⟨22829798009026406824387463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60879461357403751531699901 22829798009026406824387463)
              ·
                refine ⟨34244697013539610236581195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22829798009026406824387463 34244697013539610236581195)
                ·
                  refine ⟨51367045520309415354871793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34244697013539610236581195 51367045520309415354871793)
                  ·
                    refine ⟨38525284140232061516153845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51367045520309415354871793 38525284140232061516153845)
                    ·
                      refine ⟨3611745388146755767139423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38525284140232061516153845 3611745388146755767139423)
                      ·
                        rfl

theorem cell23_7033849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_7033849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033849 prefixEnd_7033849 := by exact prefixLift 7033849
  have htrace : WordTrace (prefixWord ++ tailWord_7033849) baseStart_7033849 baseEnd_7033849 := by
    simpa [prefixWord, tailWord_7033849, baseEnd_7033849] using wordTrace_append hprefix tailTrace_7033849
  have hstable : (prefixWord ++ tailWord_7033849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033849).length < 2 ^ (prefixWord ++ tailWord_7033849).sum := by decide
  have hdescent : baseEnd_7033849 < baseStart_7033849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033910 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7033910 : Nat := 118140960795 + 7033910 * 2 ^ 59
def prefixEnd_7033910 : Nat := 4983230072969 + 3 ^ 40 * 7033910 * 2
def baseEnd_7033910 : Nat := 3611776710466680028476643

theorem tailTrace_7033910 : CollatzResearch.WordTrace tailWord_7033910 prefixEnd_7033910 3611776710466680028476643 := by
  unfold tailWord_7033910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16034235871709552564564699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171031849298235227355356789 16034235871709552564564699)
  ·
    refine ⟨24051353807564328846847049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16034235871709552564564699 24051353807564328846847049)
    ·
      refine ⟨18038515355673246635135287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24051353807564328846847049 18038515355673246635135287)
      ·
        refine ⟨27057773033509869952702931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18038515355673246635135287 27057773033509869952702931)
        ·
          refine ⟨40586659550264804929054397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27057773033509869952702931 40586659550264804929054397)
          ·
            refine ⟨15219997331349301848395399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40586659550264804929054397 15219997331349301848395399)
            ·
              refine ⟨22829995997023952772593099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15219997331349301848395399 22829995997023952772593099)
              ·
                refine ⟨34244993995535929158889649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22829995997023952772593099 34244993995535929158889649)
                ·
                  refine ⟨25683745496651946869167237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34244993995535929158889649 25683745496651946869167237)
                  ·
                    refine ⟨4815702280622240037968857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25683745496651946869167237 4815702280622240037968857)
                    ·
                      refine ⟨3611776710466680028476643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815702280622240037968857 3611776710466680028476643)
                      ·
                        rfl

theorem cell23_7033910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7033910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033910 prefixEnd_7033910 := by exact prefixLift 7033910
  have htrace : WordTrace (prefixWord ++ tailWord_7033910) baseStart_7033910 baseEnd_7033910 := by
    simpa [prefixWord, tailWord_7033910, baseEnd_7033910] using wordTrace_append hprefix tailTrace_7033910
  have hstable : (prefixWord ++ tailWord_7033910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033910).length < 2 ^ (prefixWord ++ tailWord_7033910).sum := by decide
  have hdescent : baseEnd_7033910 < baseStart_7033910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033916 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 6]
def baseStart_7033916 : Nat := 118140960795 + 7033916 * 2 ^ 59
def prefixEnd_7033916 : Nat := 4983230072969 + 3 ^ 40 * 7033916 * 2
def baseEnd_7033916 : Nat := 401308865705623000555735

theorem tailTrace_7033916 : CollatzResearch.WordTrace tailWord_7033916 prefixEnd_7033916 401308865705623000555735 := by
  unfold tailWord_7033916
  simp only [CollatzResearch.WordTrace]
  refine ⟨128273996392665552028876801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171031995190220736038502401 128273996392665552028876801)
  ·
    refine ⟨96205497294499164021657601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128273996392665552028876801 96205497294499164021657601)
    ·
      refine ⟨72154122970874373016243201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96205497294499164021657601 72154122970874373016243201)
      ·
        refine ⟨54115592228155779762182401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72154122970874373016243201 54115592228155779762182401)
        ·
          refine ⟨40586694171116834821636801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54115592228155779762182401 40586694171116834821636801)
          ·
            refine ⟨30440020628337626116227601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40586694171116834821636801 30440020628337626116227601)
            ·
              refine ⟨22830015471253219587170701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30440020628337626116227601 22830015471253219587170701)
              ·
                refine ⟨8561255801719957345189013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22830015471253219587170701 8561255801719957345189013)
                ·
                  refine ⟨401308865705623000555735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8561255801719957345189013 401308865705623000555735)
                  ·
                    rfl

theorem cell23_7033916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_7033916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033916 prefixEnd_7033916 := by exact prefixLift 7033916
  have htrace : WordTrace (prefixWord ++ tailWord_7033916) baseStart_7033916 baseEnd_7033916 := by
    simpa [prefixWord, tailWord_7033916, baseEnd_7033916] using wordTrace_append hprefix tailTrace_7033916
  have hstable : (prefixWord ++ tailWord_7033916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033916).length < 2 ^ (prefixWord ++ tailWord_7033916).sum := by decide
  have hdescent : baseEnd_7033916 < baseStart_7033916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033950 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_7033950 : Nat := 118140960795 + 7033950 * 2 ^ 59
def prefixEnd_7033950 : Nat := 4983230072969 + 3 ^ 40 * 7033950 * 2
def baseEnd_7033950 : Nat := 401310805521428874664051

theorem tailTrace_7033950 : CollatzResearch.WordTrace tailWord_7033950 prefixEnd_7033950 401310805521428874664051 := by
  unfold tailWord_7033950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068654108400990983061413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171032821911471951909660869 32068654108400990983061413)
  ·
    refine ⟨6012872645325185809324015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32068654108400990983061413 6012872645325185809324015)
    ·
      refine ⟨9019308967987778713986023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012872645325185809324015 9019308967987778713986023)
      ·
        refine ⟨13528963451981668070979035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019308967987778713986023 13528963451981668070979035)
        ·
          refine ⟨20293445177972502106468553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528963451981668070979035 20293445177972502106468553)
          ·
            refine ⟨15220083883479376579851415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20293445177972502106468553 15220083883479376579851415)
            ·
              refine ⟨22830125825219064869777123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15220083883479376579851415 22830125825219064869777123)
              ·
                refine ⟨34245188737828597304665685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22830125825219064869777123 34245188737828597304665685)
                ·
                  refine ⟨401310805521428874664051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34245188737828597304665685 401310805521428874664051)
                  ·
                    rfl

theorem cell23_7033950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_7033950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033950 prefixEnd_7033950 := by exact prefixLift 7033950
  have htrace : WordTrace (prefixWord ++ tailWord_7033950) baseStart_7033950 baseEnd_7033950 := by
    simpa [prefixWord, tailWord_7033950, baseEnd_7033950] using wordTrace_append hprefix tailTrace_7033950
  have hstable : (prefixWord ++ tailWord_7033950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033950).length < 2 ^ (prefixWord ++ tailWord_7033950).sum := by decide
  have hdescent : baseEnd_7033950 < baseStart_7033950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033953 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_7033953 : Nat := 118140960795 + 7033953 * 2 ^ 59
def prefixEnd_7033953 : Nat := 4983230072969 + 3 ^ 40 * 7033953 * 2
def baseEnd_7033953 : Nat := 3611798790134823360238945

theorem tailTrace_7033953 : CollatzResearch.WordTrace tailWord_7033953 prefixEnd_7033953 3611798790134823360238945 := by
  unfold tailWord_7033953
  simp only [CollatzResearch.WordTrace]
  refine ⟨256549342286197059376850513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171032894857464706251233675 256549342286197059376850513)
  ·
    refine ⟨192412006714647794532637885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256549342286197059376850513 192412006714647794532637885)
    ·
      refine ⟨72154502517992922949739207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192412006714647794532637885 72154502517992922949739207)
      ·
        refine ⟨108231753776989384424608811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72154502517992922949739207 108231753776989384424608811)
        ·
          refine ⟨162347630665484076636913217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108231753776989384424608811 162347630665484076636913217)
          ·
            refine ⟨121760722999113057477684913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162347630665484076636913217 121760722999113057477684913)
            ·
              refine ⟨91320542249334793108263685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121760722999113057477684913 91320542249334793108263685)
              ·
                refine ⟨17122601671750273707799441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91320542249334793108263685 17122601671750273707799441)
                ·
                  refine ⟨12841951253812705280849581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17122601671750273707799441 12841951253812705280849581)
                  ·
                    refine ⟨4815731720179764480318593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12841951253812705280849581 4815731720179764480318593)
                    ·
                      refine ⟨3611798790134823360238945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815731720179764480318593 3611798790134823360238945)
                      ·
                        rfl

theorem cell23_7033953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_7033953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033953 prefixEnd_7033953 := by exact prefixLift 7033953
  have htrace : WordTrace (prefixWord ++ tailWord_7033953) baseStart_7033953 baseEnd_7033953 := by
    simpa [prefixWord, tailWord_7033953, baseEnd_7033953] using wordTrace_append hprefix tailTrace_7033953
  have hstable : (prefixWord ++ tailWord_7033953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033953).length < 2 ^ (prefixWord ++ tailWord_7033953).sum := by decide
  have hdescent : baseEnd_7033953 < baseStart_7033953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033976 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_7033976 : Nat := 118140960795 + 7033976 * 2 ^ 59
def prefixEnd_7033976 : Nat := 4983230072969 + 3 ^ 40 * 7033976 * 2
def baseEnd_7033976 : Nat := 1203936866729958923417113

theorem tailTrace_7033976 : CollatzResearch.WordTrace tailWord_7033976 prefixEnd_7033976 1203936866729958923417113 := by
  unfold tailWord_7033976
  simp only [CollatzResearch.WordTrace]
  refine ⟨128275090582556867152468891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171033454110075822869958521 128275090582556867152468891)
  ·
    refine ⟨192412635873835300728703337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128275090582556867152468891 192412635873835300728703337)
    ·
      refine ⟨144309476905376475546527503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192412635873835300728703337 144309476905376475546527503)
      ·
        refine ⟨216464215358064713319791255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144309476905376475546527503 216464215358064713319791255)
        ·
          refine ⟨324696323037097069979686883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216464215358064713319791255 324696323037097069979686883)
          ·
            refine ⟨487044484555645604969530325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324696323037097069979686883 487044484555645604969530325)
            ·
              refine ⟨11415105106772943866473367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 487044484555645604969530325 11415105106772943866473367)
              ·
                refine ⟨17122657660159415799710051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11415105106772943866473367 17122657660159415799710051)
                ·
                  refine ⟨25683986490239123699565077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17122657660159415799710051 25683986490239123699565077)
                  ·
                    refine ⟨1203936866729958923417113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25683986490239123699565077 1203936866729958923417113)
                    ·
                      rfl

theorem cell23_7033976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_7033976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033976 prefixEnd_7033976 := by exact prefixLift 7033976
  have htrace : WordTrace (prefixWord ++ tailWord_7033976) baseStart_7033976 baseEnd_7033976 := by
    simpa [prefixWord, tailWord_7033976, baseEnd_7033976] using wordTrace_append hprefix tailTrace_7033976
  have hstable : (prefixWord ++ tailWord_7033976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033976).length < 2 ^ (prefixWord ++ tailWord_7033976).sum := by decide
  have hdescent : baseEnd_7033976 < baseStart_7033976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033996 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7033996 : Nat := 118140960795 + 7033996 * 2 ^ 59
def prefixEnd_7033996 : Nat := 4983230072969 + 3 ^ 40 * 7033996 * 2
def baseEnd_7033996 : Nat := 3611820869802966692001247

theorem tailTrace_7033996 : CollatzResearch.WordTrace tailWord_7033996 prefixEnd_7033996 3611820869802966692001247 := by
  unfold tailWord_7033996
  simp only [CollatzResearch.WordTrace]
  refine ⟨128275455312520638860332921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171033940416694185147110561 128275455312520638860332921)
  ·
    refine ⟨96206591484390479145249691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128275455312520638860332921 96206591484390479145249691)
    ·
      refine ⟨144309887226585718717874537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96206591484390479145249691 144309887226585718717874537)
      ·
        refine ⟨108232415419939289038405903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144309887226585718717874537 108232415419939289038405903)
        ·
          refine ⟨162348623129908933557608855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108232415419939289038405903 162348623129908933557608855)
          ·
            refine ⟨243522934694863400336413283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162348623129908933557608855 243522934694863400336413283)
            ·
              refine ⟨365284402042295100504619925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243522934694863400336413283 365284402042295100504619925)
              ·
                refine ⟨17122706345732582836154059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365284402042295100504619925 17122706345732582836154059)
                ·
                  refine ⟨25684059518598874254231089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17122706345732582836154059 25684059518598874254231089)
                  ·
                    refine ⟨19263044638949155690673317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25684059518598874254231089 19263044638949155690673317)
                    ·
                      refine ⟨3611820869802966692001247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19263044638949155690673317 3611820869802966692001247)
                      ·
                        rfl

theorem cell23_7033996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7033996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033996 prefixEnd_7033996 := by exact prefixLift 7033996
  have htrace : WordTrace (prefixWord ++ tailWord_7033996) baseStart_7033996 baseEnd_7033996 := by
    simpa [prefixWord, tailWord_7033996, baseEnd_7033996] using wordTrace_append hprefix tailTrace_7033996
  have hstable : (prefixWord ++ tailWord_7033996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033996).length < 2 ^ (prefixWord ++ tailWord_7033996).sum := by decide
  have hdescent : baseEnd_7033996 < baseStart_7033996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7033999 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_7033999 : Nat := 118140960795 + 7033999 * 2 ^ 59
def prefixEnd_7033999 : Nat := 4983230072969 + 3 ^ 40 * 7033999 * 2
def baseEnd_7033999 : Nat := 3611822410244930180263733

theorem tailTrace_7033999 : CollatzResearch.WordTrace tailWord_7033999 prefixEnd_7033999 3611822410244930180263733 := by
  unfold tailWord_7033999
  simp only [CollatzResearch.WordTrace]
  refine ⟨256551020044030409233025051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171034013362686939488683367 256551020044030409233025051)
  ·
    refine ⟨384826530066045613849537577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256551020044030409233025051 384826530066045613849537577)
    ·
      refine ⟨288619897549534210387153183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384826530066045613849537577 288619897549534210387153183)
      ·
        refine ⟨432929846324301315580729775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288619897549534210387153183 432929846324301315580729775)
        ·
          refine ⟨649394769486451973371094663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432929846324301315580729775 649394769486451973371094663)
          ·
            refine ⟨974092154229677960056641995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649394769486451973371094663 974092154229677960056641995)
            ·
              refine ⟨1461138231344516940084962993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974092154229677960056641995 1461138231344516940084962993)
              ·
                refine ⟨1095853673508387705063722245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461138231344516940084962993 1095853673508387705063722245)
                ·
                  refine ⟨205472563782822694699447921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095853673508387705063722245 205472563782822694699447921)
                  ·
                    refine ⟨154104422837117021024585941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205472563782822694699447921 154104422837117021024585941)
                    ·
                      refine ⟨3611822410244930180263733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154104422837117021024585941 3611822410244930180263733)
                      ·
                        rfl

theorem cell23_7033999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_7033999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7033999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7033999 prefixEnd_7033999 := by exact prefixLift 7033999
  have htrace : WordTrace (prefixWord ++ tailWord_7033999) baseStart_7033999 baseEnd_7033999 := by
    simpa [prefixWord, tailWord_7033999, baseEnd_7033999] using wordTrace_append hprefix tailTrace_7033999
  have hstable : (prefixWord ++ tailWord_7033999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7033999).length < 2 ^ (prefixWord ++ tailWord_7033999).sum := by decide
  have hdescent : baseEnd_7033999 < baseStart_7033999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7033999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034003 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 3]
def baseStart_7034003 : Nat := 118140960795 + 7034003 * 2 ^ 59
def prefixEnd_7034003 : Nat := 4983230072969 + 3 ^ 40 * 7034003 * 2
def baseEnd_7034003 : Nat := 3611824464167548164613715

theorem tailTrace_7034003 : CollatzResearch.WordTrace tailWord_7034003 prefixEnd_7034003 3611824464167548164613715 := by
  unfold tailWord_7034003
  simp only [CollatzResearch.WordTrace]
  refine ⟨256551165936015917916170663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171034110624010611944113775 256551165936015917916170663)
  ·
    refine ⟨384826748904023876874255995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256551165936015917916170663 384826748904023876874255995)
    ·
      refine ⟨577240123356035815311383993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384826748904023876874255995 577240123356035815311383993)
      ·
        refine ⟨432930092517026861483537995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577240123356035815311383993 432930092517026861483537995)
        ·
          refine ⟨649395138775540292225306993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432930092517026861483537995 649395138775540292225306993)
          ·
            refine ⟨487046354081655219168980245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649395138775540292225306993 487046354081655219168980245)
            ·
              refine ⟨22830297847577588398545949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 487046354081655219168980245 22830297847577588398545949)
              ·
                refine ⟨8561361692841595649454731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22830297847577588398545949 8561361692841595649454731)
                ·
                  refine ⟨12842042539262393474182097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8561361692841595649454731 12842042539262393474182097)
                  ·
                    refine ⟨9631531904446795105636573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12842042539262393474182097 9631531904446795105636573)
                    ·
                      refine ⟨3611824464167548164613715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631531904446795105636573 3611824464167548164613715)
                      ·
                        rfl

theorem cell23_7034003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_7034003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034003 prefixEnd_7034003 := by exact prefixLift 7034003
  have htrace : WordTrace (prefixWord ++ tailWord_7034003) baseStart_7034003 baseEnd_7034003 := by
    simpa [prefixWord, tailWord_7034003, baseEnd_7034003] using wordTrace_append hprefix tailTrace_7034003
  have hstable : (prefixWord ++ tailWord_7034003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034003).length < 2 ^ (prefixWord ++ tailWord_7034003).sum := by decide
  have hdescent : baseEnd_7034003 < baseStart_7034003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034023 : List Nat := [1, 1, 6, 2, 1, 2, 2, 8]
def baseStart_7034023 : Nat := 118140960795 + 7034023 * 2 ^ 59
def prefixEnd_7034023 : Nat := 4983230072969 + 3 ^ 40 * 7034023 * 2
def baseEnd_7034023 : Nat := 133771656806690299494949

theorem tailTrace_7034023 : CollatzResearch.WordTrace tailWord_7034023 prefixEnd_7034023 133771656806690299494949 := by
  unfold tailWord_7034023
  simp only [CollatzResearch.WordTrace]
  refine ⟨256551895395943461331898723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171034596930628974221265815 256551895395943461331898723)
  ·
    refine ⟨384827843093915191997848085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256551895395943461331898723 384827843093915191997848085)
    ·
      refine ⟨18038805145027274624899129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 384827843093915191997848085 18038805145027274624899129)
      ·
        refine ⟨13529103858770455968674347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18038805145027274624899129 13529103858770455968674347)
        ·
          refine ⟨20293655788155683953011521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13529103858770455968674347 20293655788155683953011521)
          ·
            refine ⟨15220241841116762964758641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20293655788155683953011521 15220241841116762964758641)
            ·
              refine ⟨11415181380837572223568981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15220241841116762964758641 11415181380837572223568981)
              ·
                refine ⟨133771656806690299494949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11415181380837572223568981 133771656806690299494949)
                ·
                  rfl

theorem cell23_7034023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 8].length) (baseStart_7034023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034023 prefixEnd_7034023 := by exact prefixLift 7034023
  have htrace : WordTrace (prefixWord ++ tailWord_7034023) baseStart_7034023 baseEnd_7034023 := by
    simpa [prefixWord, tailWord_7034023, baseEnd_7034023] using wordTrace_append hprefix tailTrace_7034023
  have hstable : (prefixWord ++ tailWord_7034023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034023).length < 2 ^ (prefixWord ++ tailWord_7034023).sum := by decide
  have hdescent : baseEnd_7034023 < baseStart_7034023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034073 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 5, 4, 2]
def baseStart_7034073 : Nat := 118140960795 + 7034073 * 2 ^ 59
def prefixEnd_7034073 : Nat := 4983230072969 + 3 ^ 40 * 7034073 * 2
def baseEnd_7034073 : Nat := 3611860407813362890738393

theorem tailTrace_7034073 : CollatzResearch.WordTrace tailWord_7034073 prefixEnd_7034073 3611860407813362890738393 := by
  unfold tailWord_7034073
  simp only [CollatzResearch.WordTrace]
  refine ⟨256553719045762319871218873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171035812697174879914145915 256553719045762319871218873)
  ·
    refine ⟨192415289284321739903414155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256553719045762319871218873 192415289284321739903414155)
    ·
      refine ⟨288622933926482609855121233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192415289284321739903414155 288622933926482609855121233)
      ·
        refine ⟨216467200444861957391340925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288622933926482609855121233 216467200444861957391340925)
        ·
          refine ⟨81175200166823234021752847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216467200444861957391340925 81175200166823234021752847)
          ·
            refine ⟨121762800250234851032629271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81175200166823234021752847 121762800250234851032629271)
            ·
              refine ⟨182644200375352276548943907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121762800250234851032629271 182644200375352276548943907)
              ·
                refine ⟨273966300563028414823415861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182644200375352276548943907 273966300563028414823415861)
                ·
                  refine ⟨25684340677783913889695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273966300563028414823415861 25684340677783913889695237)
                  ·
                    refine ⟨4815813877084483854317857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25684340677783913889695237 4815813877084483854317857)
                    ·
                      refine ⟨3611860407813362890738393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815813877084483854317857 3611860407813362890738393)
                      ·
                        rfl

theorem cell23_7034073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_7034073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034073 prefixEnd_7034073 := by exact prefixLift 7034073
  have htrace : WordTrace (prefixWord ++ tailWord_7034073) baseStart_7034073 baseEnd_7034073 := by
    simpa [prefixWord, tailWord_7034073, baseEnd_7034073] using wordTrace_append hprefix tailTrace_7034073
  have hstable : (prefixWord ++ tailWord_7034073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034073).length < 2 ^ (prefixWord ++ tailWord_7034073).sum := by decide
  have hdescent : baseEnd_7034073 < baseStart_7034073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034090 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_7034090 : Nat := 118140960795 + 7034090 * 2 ^ 59
def prefixEnd_7034090 : Nat := 4983230072969 + 3 ^ 40 * 7034090 * 2
def baseEnd_7034090 : Nat := 3611869136984489324225815

theorem tailTrace_7034090 : CollatzResearch.WordTrace tailWord_7034090 prefixEnd_7034090 3611869136984489324225815 := by
  unfold tailWord_7034090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64138584771675182943646931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171036226057800487849725149 64138584771675182943646931)
  ·
    refine ⟨96207877157512774415470397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64138584771675182943646931 96207877157512774415470397)
    ·
      refine ⟨36077953934067290405801399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96207877157512774415470397 36077953934067290405801399)
      ·
        refine ⟨54116930901100935608702099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36077953934067290405801399 54116930901100935608702099)
        ·
          refine ⟨81175396351651403413053149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54116930901100935608702099 81175396351651403413053149)
          ·
            refine ⟨30440773631869276279894931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81175396351651403413053149 30440773631869276279894931)
            ·
              refine ⟨45661160447803914419842397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30440773631869276279894931 45661160447803914419842397)
              ·
                refine ⟨17122935167926467907440899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45661160447803914419842397 17122935167926467907440899)
                ·
                  refine ⟨25684402751889701861161349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17122935167926467907440899 25684402751889701861161349)
                  ·
                    refine ⟨4815825515979319098967753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25684402751889701861161349 4815825515979319098967753)
                    ·
                      refine ⟨3611869136984489324225815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815825515979319098967753 3611869136984489324225815)
                      ·
                        rfl

theorem cell23_7034090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_7034090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034090 prefixEnd_7034090 := by exact prefixLift 7034090
  have htrace : WordTrace (prefixWord ++ tailWord_7034090) baseStart_7034090 baseEnd_7034090 := by
    simpa [prefixWord, tailWord_7034090, baseEnd_7034090] using wordTrace_append hprefix tailTrace_7034090
  have hstable : (prefixWord ++ tailWord_7034090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034090).length < 2 ^ (prefixWord ++ tailWord_7034090).sum := by decide
  have hdescent : baseEnd_7034090 < baseStart_7034090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034123 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3]
def baseStart_7034123 : Nat := 118140960795 + 7034123 * 2 ^ 59
def prefixEnd_7034123 : Nat := 4983230072969 + 3 ^ 40 * 7034123 * 2
def baseEnd_7034123 : Nat := 3611886081846087695113163

theorem tailTrace_7034123 : CollatzResearch.WordTrace tailWord_7034123 prefixEnd_7034123 3611886081846087695113163 := by
  unfold tailWord_7034123
  simp only [CollatzResearch.WordTrace]
  refine ⟨256555542695581178410539023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171037028463720785607026015 256555542695581178410539023)
  ·
    refine ⟨384833314043371767615808535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256555542695581178410539023 384833314043371767615808535)
    ·
      refine ⟨577249971065057651423712803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384833314043371767615808535 577249971065057651423712803)
      ·
        refine ⟨865874956597586477135569205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577249971065057651423712803 865874956597586477135569205)
        ·
          refine ⟨81175777181023732231459613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 865874956597586477135569205 81175777181023732231459613)
          ·
            refine ⟨30440916442883899586797355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81175777181023732231459613 30440916442883899586797355)
            ·
              refine ⟨45661374664325849380196033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30440916442883899586797355 45661374664325849380196033)
              ·
                refine ⟨34246030998244387035147025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45661374664325849380196033 34246030998244387035147025)
                ·
                  refine ⟨25684523248683290276360269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34246030998244387035147025 25684523248683290276360269)
                  ·
                    refine ⟨9631696218256233853635101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25684523248683290276360269 9631696218256233853635101)
                    ·
                      refine ⟨3611886081846087695113163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631696218256233853635101 3611886081846087695113163)
                      ·
                        rfl

theorem cell23_7034123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3].length) (baseStart_7034123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034123 prefixEnd_7034123 := by exact prefixLift 7034123
  have htrace : WordTrace (prefixWord ++ tailWord_7034123) baseStart_7034123 baseEnd_7034123 := by
    simpa [prefixWord, tailWord_7034123, baseEnd_7034123] using wordTrace_append hprefix tailTrace_7034123
  have hstable : (prefixWord ++ tailWord_7034123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034123).length < 2 ^ (prefixWord ++ tailWord_7034123).sum := by decide
  have hdescent : baseEnd_7034123 < baseStart_7034123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034124 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_7034124 : Nat := 118140960795 + 7034124 * 2 ^ 59
def prefixEnd_7034124 : Nat := 4983230072969 + 3 ^ 40 * 7034124 * 2
def baseEnd_7034124 : Nat := 3611886595326742191200659

theorem tailTrace_7034124 : CollatzResearch.WordTrace tailWord_7034124 prefixEnd_7034124 3611886595326742191200659 := by
  unfold tailWord_7034124
  simp only [CollatzResearch.WordTrace]
  refine ⟨128277789584288777790662713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171037052779051703720883617 128277789584288777790662713)
  ·
    refine ⟨96208342188216583342997035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128277789584288777790662713 96208342188216583342997035)
    ·
      refine ⟨144312513282324875014495553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96208342188216583342997035 144312513282324875014495553)
      ·
        refine ⟨108234384961743656260871665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144312513282324875014495553 108234384961743656260871665)
        ·
          refine ⟨81175788721307742195653749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108234384961743656260871665 81175788721307742195653749)
          ·
            refine ⟨7610230192622600830842539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81175788721307742195653749 7610230192622600830842539)
            ·
              refine ⟨11415345288933901246263809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610230192622600830842539 11415345288933901246263809)
              ·
                refine ⟨8561508966700425934697857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11415345288933901246263809 8561508966700425934697857)
                ·
                  refine ⟨6421131725025319451023393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8561508966700425934697857 6421131725025319451023393)
                  ·
                    refine ⟨4815848793768989588267545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421131725025319451023393 4815848793768989588267545)
                    ·
                      refine ⟨3611886595326742191200659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815848793768989588267545 3611886595326742191200659)
                      ·
                        rfl

theorem cell23_7034124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_7034124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034124 prefixEnd_7034124 := by exact prefixLift 7034124
  have htrace : WordTrace (prefixWord ++ tailWord_7034124) baseStart_7034124 baseEnd_7034124 := by
    simpa [prefixWord, tailWord_7034124, baseEnd_7034124] using wordTrace_append hprefix tailTrace_7034124
  have hstable : (prefixWord ++ tailWord_7034124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034124).length < 2 ^ (prefixWord ++ tailWord_7034124).sum := by decide
  have hdescent : baseEnd_7034124 < baseStart_7034124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034141 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7034141 : Nat := 118140960795 + 7034141 * 2 ^ 59
def prefixEnd_7034141 : Nat := 4983230072969 + 3 ^ 40 * 7034141 * 2
def baseEnd_7034141 : Nat := 3611895324497868624688081

theorem tailTrace_7034141 : CollatzResearch.WordTrace tailWord_7034141 prefixEnd_7034141 3611895324497868624688081 := by
  unfold tailWord_7034141
  simp only [CollatzResearch.WordTrace]
  refine ⟨256556199209515967484694277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171037466139677311656462851 256556199209515967484694277)
  ·
    refine ⟨48104287351784243903380177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256556199209515967484694277 48104287351784243903380177)
    ·
      refine ⟨36078215513838182927535133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48104287351784243903380177 36078215513838182927535133)
      ·
        refine ⟨13529330817689318597825675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36078215513838182927535133 13529330817689318597825675)
        ·
          refine ⟨20293996226533977896738513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13529330817689318597825675 20293996226533977896738513)
          ·
            refine ⟨15220497169900483422553885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20293996226533977896738513 15220497169900483422553885)
            ·
              refine ⟨5707686438712681283457707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15220497169900483422553885 5707686438712681283457707)
              ·
                refine ⟨8561529658069021925186561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707686438712681283457707 8561529658069021925186561)
                ·
                  refine ⟨6421147243551766443889921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8561529658069021925186561 6421147243551766443889921)
                  ·
                    refine ⟨4815860432663824832917441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421147243551766443889921 4815860432663824832917441)
                    ·
                      refine ⟨3611895324497868624688081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815860432663824832917441 3611895324497868624688081)
                      ·
                        rfl

theorem cell23_7034141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7034141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034141 prefixEnd_7034141 := by exact prefixLift 7034141
  have htrace : WordTrace (prefixWord ++ tailWord_7034141) baseStart_7034141 baseEnd_7034141 := by
    simpa [prefixWord, tailWord_7034141, baseEnd_7034141] using wordTrace_append hprefix tailTrace_7034141
  have hstable : (prefixWord ++ tailWord_7034141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034141).length < 2 ^ (prefixWord ++ tailWord_7034141).sum := by decide
  have hdescent : baseEnd_7034141 < baseStart_7034141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034156 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_7034156 : Nat := 118140960795 + 7034156 * 2 ^ 59
def prefixEnd_7034156 : Nat := 4983230072969 + 3 ^ 40 * 7034156 * 2
def baseEnd_7034156 : Nat := 1203967675569228688666837

theorem tailTrace_7034156 : CollatzResearch.WordTrace tailWord_7034156 prefixEnd_7034156 1203967675569228688666837 := by
  unfold tailWord_7034156
  simp only [CollatzResearch.WordTrace]
  refine ⟨128278373152230812523245161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171037830869641083364326881 128278373152230812523245161)
  ·
    refine ⟨96208779864173109392433871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128278373152230812523245161 96208779864173109392433871)
    ·
      refine ⟨144313169796259664088650807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96208779864173109392433871 144313169796259664088650807)
      ·
        refine ⟨216469754694389496132976211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144313169796259664088650807 216469754694389496132976211)
        ·
          refine ⟨324704632041584244199464317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216469754694389496132976211 324704632041584244199464317)
          ·
            refine ⟨121764237015594091574799119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324704632041584244199464317 121764237015594091574799119)
            ·
              refine ⟨182646355523391137362198679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121764237015594091574799119 182646355523391137362198679)
              ·
                refine ⟨273969533285086706043298019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182646355523391137362198679 273969533285086706043298019)
                ·
                  refine ⟨410954299927630059064947029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273969533285086706043298019 410954299927630059064947029)
                  ·
                    refine ⟨1203967675569228688666837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 410954299927630059064947029 1203967675569228688666837)
                    ·
                      rfl

theorem cell23_7034156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_7034156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034156 prefixEnd_7034156 := by exact prefixLift 7034156
  have htrace : WordTrace (prefixWord ++ tailWord_7034156) baseStart_7034156 baseEnd_7034156 := by
    simpa [prefixWord, tailWord_7034156, baseEnd_7034156] using wordTrace_append hprefix tailTrace_7034156
  have hstable : (prefixWord ++ tailWord_7034156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034156).length < 2 ^ (prefixWord ++ tailWord_7034156).sum := by decide
  have hdescent : baseEnd_7034156 < baseStart_7034156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034163 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_7034163 : Nat := 118140960795 + 7034163 * 2 ^ 59
def prefixEnd_7034163 : Nat := 4983230072969 + 3 ^ 40 * 7034163 * 2
def baseEnd_7034163 : Nat := 3611906621072267538612979

theorem tailTrace_7034163 : CollatzResearch.WordTrace tailWord_7034163 prefixEnd_7034163 3611906621072267538612979 := by
  unfold tailWord_7034163
  simp only [CollatzResearch.WordTrace]
  refine ⟨256557001615436265241995143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171038001076957510161330095 256557001615436265241995143)
  ·
    refine ⟨384835502423154397862992715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256557001615436265241995143 384835502423154397862992715)
    ·
      refine ⟨577253253634731596794489073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384835502423154397862992715 577253253634731596794489073)
      ·
        refine ⟨432939940226048697595866805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577253253634731596794489073 432939940226048697595866805)
        ·
          refine ⟨40588119396192065399612513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432939940226048697595866805 40588119396192065399612513)
          ·
            refine ⟨30441089547144049049709385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40588119396192065399612513 30441089547144049049709385)
            ·
              refine ⟨22830817160358036787282039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30441089547144049049709385 22830817160358036787282039)
              ·
                refine ⟨34246225740537055180923059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22830817160358036787282039 34246225740537055180923059)
                ·
                  refine ⟨51369338610805582771384589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34246225740537055180923059 51369338610805582771384589)
                  ·
                    refine ⟨19263501979052093539269221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51369338610805582771384589 19263501979052093539269221)
                    ·
                      refine ⟨3611906621072267538612979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19263501979052093539269221 3611906621072267538612979)
                      ·
                        rfl

theorem cell23_7034163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_7034163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034163 prefixEnd_7034163 := by exact prefixLift 7034163
  have htrace : WordTrace (prefixWord ++ tailWord_7034163) baseStart_7034163 baseEnd_7034163 := by
    simpa [prefixWord, tailWord_7034163, baseEnd_7034163] using wordTrace_append hprefix tailTrace_7034163
  have hstable : (prefixWord ++ tailWord_7034163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034163).length < 2 ^ (prefixWord ++ tailWord_7034163).sum := by decide
  have hdescent : baseEnd_7034163 < baseStart_7034163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034264 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7034264 : Nat := 118140960795 + 7034264 * 2 ^ 59
def prefixEnd_7034264 : Nat := 4983230072969 + 3 ^ 40 * 7034264 * 2
def baseEnd_7034264 : Nat := 3611958482618371643450015

theorem tailTrace_7034264 : CollatzResearch.WordTrace tailWord_7034264 prefixEnd_7034264 3611958482618371643450015 := by
  unfold tailWord_7034264
  simp only [CollatzResearch.WordTrace]
  refine ⟨128280342694035179745710923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171040456925380239660947897 128280342694035179745710923)
  ·
    refine ⟨192420514041052769618566385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128280342694035179745710923 192420514041052769618566385)
    ·
      refine ⟨144315385530789577213924789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192420514041052769618566385 144315385530789577213924789)
      ·
        refine ⟨13529567393511522863805449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144315385530789577213924789 13529567393511522863805449)
        ·
          refine ⟨10147175545133642147854087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13529567393511522863805449 10147175545133642147854087)
          ·
            refine ⟨15220763317700463221781131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10147175545133642147854087 15220763317700463221781131)
            ·
              refine ⟨22831144976550694832671697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15220763317700463221781131 22831144976550694832671697)
              ·
                refine ⟨17123358732413021124503773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22831144976550694832671697 17123358732413021124503773)
                ·
                  refine ⟨6421259524654882921688915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17123358732413021124503773 6421259524654882921688915)
                  ·
                    refine ⟨9631889286982324382533373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6421259524654882921688915 9631889286982324382533373)
                    ·
                      refine ⟨3611958482618371643450015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631889286982324382533373 3611958482618371643450015)
                      ·
                        rfl

theorem cell23_7034264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7034264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034264 prefixEnd_7034264 := by exact prefixLift 7034264
  have htrace : WordTrace (prefixWord ++ tailWord_7034264) baseStart_7034264 baseEnd_7034264 := by
    simpa [prefixWord, tailWord_7034264, baseEnd_7034264] using wordTrace_append hprefix tailTrace_7034264
  have hstable : (prefixWord ++ tailWord_7034264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034264).length < 2 ^ (prefixWord ++ tailWord_7034264).sum := by decide
  have hdescent : baseEnd_7034264 < baseStart_7034264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034274 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_7034274 : Nat := 118140960795 + 7034274 * 2 ^ 59
def prefixEnd_7034274 : Nat := 4983230072969 + 3 ^ 40 * 7034274 * 2
def baseEnd_7034274 : Nat := 3611963617424916604324969

theorem tailTrace_7034274 : CollatzResearch.WordTrace tailWord_7034274 prefixEnd_7034274 3611963617424916604324969 := by
  unfold tailWord_7034274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140262529508532799821469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171040700078689420799523917 64140262529508532799821469)
  ·
    refine ⟨24052598448565699799933051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64140262529508532799821469 24052598448565699799933051)
    ·
      refine ⟨36078897672848549699899577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24052598448565699799933051 36078897672848549699899577)
      ·
        refine ⟨27059173254636412274924683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36078897672848549699899577 27059173254636412274924683)
        ·
          refine ⟨40588759881954618412387025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27059173254636412274924683 40588759881954618412387025)
          ·
            refine ⟨30441569911465963809290269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40588759881954618412387025 30441569911465963809290269)
            ·
              refine ⟨11415588716799736428483851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30441569911465963809290269 11415588716799736428483851)
              ·
                refine ⟨17123383075199604642725777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11415588716799736428483851 17123383075199604642725777)
                ·
                  refine ⟨12842537306399703482044333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17123383075199604642725777 12842537306399703482044333)
                  ·
                    refine ⟨4815951489899888805766625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12842537306399703482044333 4815951489899888805766625)
                    ·
                      refine ⟨3611963617424916604324969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4815951489899888805766625 3611963617424916604324969)
                      ·
                        rfl

theorem cell23_7034274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_7034274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034274 prefixEnd_7034274 := by exact prefixLift 7034274
  have htrace : WordTrace (prefixWord ++ tailWord_7034274) baseStart_7034274 baseEnd_7034274 := by
    simpa [prefixWord, tailWord_7034274, baseEnd_7034274] using wordTrace_append hprefix tailTrace_7034274
  have hstable : (prefixWord ++ tailWord_7034274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034274).length < 2 ^ (prefixWord ++ tailWord_7034274).sum := by decide
  have hdescent : baseEnd_7034274 < baseStart_7034274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034283 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_7034283 : Nat := 118140960795 + 7034283 * 2 ^ 59
def prefixEnd_7034283 : Nat := 4983230072969 + 3 ^ 40 * 7034283 * 2
def baseEnd_7034283 : Nat := 3611968238750807069112427

theorem tailTrace_7034283 : CollatzResearch.WordTrace tailWord_7034283 prefixEnd_7034283 3611968238750807069112427 := by
  unfold tailWord_7034283
  simp only [CollatzResearch.WordTrace]
  refine ⟨256561378375001525736363503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171040918916667683824242335 256561378375001525736363503)
  ·
    refine ⟨384842067562502288604545255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256561378375001525736363503 384842067562502288604545255)
    ·
      refine ⟨577263101343753432906817883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384842067562502288604545255 577263101343753432906817883)
      ·
        refine ⟨865894652015630149360226825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577263101343753432906817883 865894652015630149360226825)
        ·
          refine ⟨649420989011722612020170119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865894652015630149360226825 649420989011722612020170119)
          ·
            refine ⟨974131483517583918030255179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649420989011722612020170119 974131483517583918030255179)
            ·
              refine ⟨1461197225276375877045382769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974131483517583918030255179 1461197225276375877045382769)
              ·
                refine ⟨1095897918957281907784037077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461197225276375877045382769 1095897918957281907784037077)
                ·
                  refine ⟨25685107475561294713688369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1095897918957281907784037077 25685107475561294713688369)
                  ·
                    refine ⟨19263830606670971035266277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25685107475561294713688369 19263830606670971035266277)
                    ·
                      refine ⟨3611968238750807069112427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19263830606670971035266277 3611968238750807069112427)
                      ·
                        rfl

theorem cell23_7034283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_7034283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034283 prefixEnd_7034283 := by exact prefixLift 7034283
  have htrace : WordTrace (prefixWord ++ tailWord_7034283) baseStart_7034283 baseEnd_7034283 := by
    simpa [prefixWord, tailWord_7034283, baseEnd_7034283] using wordTrace_append hprefix tailTrace_7034283
  have hstable : (prefixWord ++ tailWord_7034283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034283).length < 2 ^ (prefixWord ++ tailWord_7034283).sum := by decide
  have hdescent : baseEnd_7034283 < baseStart_7034283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034290 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_7034290 : Nat := 118140960795 + 7034290 * 2 ^ 59
def prefixEnd_7034290 : Nat := 4983230072969 + 3 ^ 40 * 7034290 * 2
def baseEnd_7034290 : Nat := 3611971833115388541724895

theorem tailTrace_7034290 : CollatzResearch.WordTrace tailWord_7034290 prefixEnd_7034290 3611971833115388541724895 := by
  unfold tailWord_7034290
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140408421494041482967081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171041089123984110621245549 64140408421494041482967081)
  ·
    refine ⟨48105306316120531112225311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64140408421494041482967081 48105306316120531112225311)
    ·
      refine ⟨72157959474180796668337967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48105306316120531112225311 72157959474180796668337967)
      ·
        refine ⟨108236939211271195002506951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72157959474180796668337967 108236939211271195002506951)
        ·
          refine ⟨162355408816906792503760427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108236939211271195002506951 162355408816906792503760427)
          ·
            refine ⟨243533113225360188755640641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162355408816906792503760427 243533113225360188755640641)
            ·
              refine ⟨182649834919020141566730481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243533113225360188755640641 182649834919020141566730481)
              ·
                refine ⟨136987376189265106175047861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182649834919020141566730481 136987376189265106175047861)
                ·
                  refine ⟨12842566517743603703910737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136987376189265106175047861 12842566517743603703910737)
                  ·
                    refine ⟨9631924888307702777933053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12842566517743603703910737 9631924888307702777933053)
                    ·
                      refine ⟨3611971833115388541724895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631924888307702777933053 3611971833115388541724895)
                      ·
                        rfl

theorem cell23_7034290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_7034290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034290 prefixEnd_7034290 := by exact prefixLift 7034290
  have htrace : WordTrace (prefixWord ++ tailWord_7034290) baseStart_7034290 baseEnd_7034290 := by
    simpa [prefixWord, tailWord_7034290, baseEnd_7034290] using wordTrace_append hprefix tailTrace_7034290
  have hstable : (prefixWord ++ tailWord_7034290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034290).length < 2 ^ (prefixWord ++ tailWord_7034290).sum := by decide
  have hdescent : baseEnd_7034290 < baseStart_7034290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034297 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_7034297 : Nat := 118140960795 + 7034297 * 2 ^ 59
def prefixEnd_7034297 : Nat := 4983230072969 + 3 ^ 40 * 7034297 * 2
def baseEnd_7034297 : Nat := 1203991809159990004779121

theorem tailTrace_7034297 : CollatzResearch.WordTrace tailWord_7034297 prefixEnd_7034297 1203991809159990004779121 := by
  unfold tailWord_7034297
  simp only [CollatzResearch.WordTrace]
  refine ⟨256561888996950806127373145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171041259331300537418248763 256561888996950806127373145)
  ·
    refine ⟨192421416747713104595529859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256561888996950806127373145 192421416747713104595529859)
    ·
      refine ⟨288632125121569656893294789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192421416747713104595529859 288632125121569656893294789)
      ·
        refine ⟨54118523460294310667492773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288632125121569656893294789 54118523460294310667492773)
        ·
          refine ⟨10147223148805183250154895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54118523460294310667492773 10147223148805183250154895)
          ·
            refine ⟨15220834723207774875232343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10147223148805183250154895 15220834723207774875232343)
            ·
              refine ⟨22831252084811662312848515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15220834723207774875232343 22831252084811662312848515)
              ·
                refine ⟨34246878127217493469272773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22831252084811662312848515 34246878127217493469272773)
                ·
                  refine ⟨6421289648853280025488645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34246878127217493469272773 6421289648853280025488645)
                  ·
                    refine ⟨1203991809159990004779121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421289648853280025488645 1203991809159990004779121)
                    ·
                      rfl

theorem cell23_7034297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_7034297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034297 prefixEnd_7034297 := by exact prefixLift 7034297
  have htrace : WordTrace (prefixWord ++ tailWord_7034297) baseStart_7034297 baseEnd_7034297 := by
    simpa [prefixWord, tailWord_7034297, baseEnd_7034297] using wordTrace_append hprefix tailTrace_7034297
  have hstable : (prefixWord ++ tailWord_7034297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034297).length < 2 ^ (prefixWord ++ tailWord_7034297).sum := by decide
  have hdescent : baseEnd_7034297 < baseStart_7034297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034314 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_7034314 : Nat := 118140960795 + 7034314 * 2 ^ 59
def prefixEnd_7034314 : Nat := 4983230072969 + 3 ^ 40 * 7034314 * 2
def baseEnd_7034314 : Nat := 1203994718883698815941595

theorem tailTrace_7034314 : CollatzResearch.WordTrace tailWord_7034314 prefixEnd_7034314 1203994718883698815941595 := by
  unfold tailWord_7034314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140627259472304507685499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171041672691926145353827997 64140627259472304507685499)
  ·
    refine ⟨96210940889208456761528249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64140627259472304507685499 96210940889208456761528249)
    ·
      refine ⟨72158205666906342571146187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96210940889208456761528249 72158205666906342571146187)
      ·
        refine ⟨108237308500359513856719281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72158205666906342571146187 108237308500359513856719281)
        ·
          refine ⟨81177981375269635392539461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108237308500359513856719281 81177981375269635392539461)
          ·
            refine ⟨15220871507863056636101149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81177981375269635392539461 15220871507863056636101149)
            ·
              refine ⟨5707826815448646238537931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15220871507863056636101149 5707826815448646238537931)
              ·
                refine ⟨8561740223172969357806897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707826815448646238537931 8561740223172969357806897)
                ·
                  refine ⟨6421305167379727018355173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8561740223172969357806897 6421305167379727018355173)
                  ·
                    refine ⟨1203994718883698815941595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421305167379727018355173 1203994718883698815941595)
                    ·
                      rfl

theorem cell23_7034314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_7034314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034314 prefixEnd_7034314 := by exact prefixLift 7034314
  have htrace : WordTrace (prefixWord ++ tailWord_7034314) baseStart_7034314 baseEnd_7034314 := by
    simpa [prefixWord, tailWord_7034314, baseEnd_7034314] using wordTrace_append hprefix tailTrace_7034314
  have hstable : (prefixWord ++ tailWord_7034314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034314).length < 2 ^ (prefixWord ++ tailWord_7034314).sum := by decide
  have hdescent : baseEnd_7034314 < baseStart_7034314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034337 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_7034337 : Nat := 118140960795 + 7034337 * 2 ^ 59
def prefixEnd_7034337 : Nat := 4983230072969 + 3 ^ 40 * 7034337 * 2
def baseEnd_7034337 : Nat := 3611995966706149857837179

theorem tailTrace_7034337 : CollatzResearch.WordTrace tailWord_7034337 prefixEnd_7034337 3611995966706149857837179 := by
  unfold tailWord_7034337
  simp only [CollatzResearch.WordTrace]
  refine ⟨256563347916805892958829265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171042231944537261972552843 256563347916805892958829265)
  ·
    refine ⟨192422510937604419719121949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256563347916805892958829265 192422510937604419719121949)
    ·
      refine ⟨72158441601601657394670731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192422510937604419719121949 72158441601601657394670731)
      ·
        refine ⟨108237662402402486092006097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72158441601601657394670731 108237662402402486092006097)
        ·
          refine ⟨81178246801801864569004573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108237662402402486092006097 81178246801801864569004573)
          ·
            refine ⟨30441842550675699213376715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81178246801801864569004573 30441842550675699213376715)
            ·
              refine ⟨45662763826013548820065073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30441842550675699213376715 45662763826013548820065073)
              ·
                refine ⟨34247072869510161615048805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45662763826013548820065073 34247072869510161615048805)
                ·
                  refine ⟨6421326163033155302821651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34247072869510161615048805 6421326163033155302821651)
                  ·
                    refine ⟨9631989244549732954232477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6421326163033155302821651 9631989244549732954232477)
                    ·
                      refine ⟨3611995966706149857837179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9631989244549732954232477 3611995966706149857837179)
                      ·
                        rfl

theorem cell23_7034337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_7034337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034337 prefixEnd_7034337 := by exact prefixLift 7034337
  have htrace : WordTrace (prefixWord ++ tailWord_7034337) baseStart_7034337 baseEnd_7034337 := by
    simpa [prefixWord, tailWord_7034337, baseEnd_7034337] using wordTrace_append hprefix tailTrace_7034337
  have hstable : (prefixWord ++ tailWord_7034337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034337).length < 2 ^ (prefixWord ++ tailWord_7034337).sum := by decide
  have hdescent : baseEnd_7034337 < baseStart_7034337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034350 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7034350 : Nat := 118140960795 + 7034350 * 2 ^ 59
def prefixEnd_7034350 : Nat := 4983230072969 + 3 ^ 40 * 7034350 * 2
def baseEnd_7034350 : Nat := 3612002641954658306974619

theorem tailTrace_7034350 : CollatzResearch.WordTrace tailWord_7034350 prefixEnd_7034350 3612002641954658306974619 := by
  unfold tailWord_7034350
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070477758219849522381563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171042548043839197452701669 32070477758219849522381563)
  ·
    refine ⟨48105716637329774283572345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32070477758219849522381563 48105716637329774283572345)
    ·
      refine ⟨36079287477997330712679259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48105716637329774283572345 36079287477997330712679259)
      ·
        refine ⟨54118931216995996069018889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36079287477997330712679259 54118931216995996069018889)
        ·
          refine ⟨40589198412746997051764167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54118931216995996069018889 40589198412746997051764167)
          ·
            refine ⟨60883797619120495577646251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40589198412746997051764167 60883797619120495577646251)
            ·
              refine ⟨91325696428680743366469377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60883797619120495577646251 91325696428680743366469377)
              ·
                refine ⟨68494272321510557524852033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91325696428680743366469377 68494272321510557524852033)
                ·
                  refine ⟨51370704241132918143639025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68494272321510557524852033 51370704241132918143639025)
                  ·
                    refine ⟨38528028180849688607729269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51370704241132918143639025 38528028180849688607729269)
                    ·
                      refine ⟨3612002641954658306974619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38528028180849688607729269 3612002641954658306974619)
                      ·
                        rfl

theorem cell23_7034350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7034350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034350 prefixEnd_7034350 := by exact prefixLift 7034350
  have htrace : WordTrace (prefixWord ++ tailWord_7034350) baseStart_7034350 baseEnd_7034350 := by
    simpa [prefixWord, tailWord_7034350, baseEnd_7034350] using wordTrace_append hprefix tailTrace_7034350
  have hstable : (prefixWord ++ tailWord_7034350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034350).length < 2 ^ (prefixWord ++ tailWord_7034350).sum := by decide
  have hdescent : baseEnd_7034350 < baseStart_7034350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034354 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7034354 : Nat := 118140960795 + 7034354 * 2 ^ 59
def prefixEnd_7034354 : Nat := 4983230072969 + 3 ^ 40 * 7034354 * 2
def baseEnd_7034354 : Nat := 3612004695877276291324601

theorem tailTrace_7034354 : CollatzResearch.WordTrace tailWord_7034354 prefixEnd_7034354 3612004695877276291324601 := by
  unfold tailWord_7034354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140991989436076215549529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171042645305162869908132077 64140991989436076215549529)
  ·
    refine ⟨48105743992077057161662147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64140991989436076215549529 48105743992077057161662147)
    ·
      refine ⟨72158615988115585742493221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48105743992077057161662147 72158615988115585742493221)
      ·
        refine ⟨13529740497771672326717479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72158615988115585742493221 13529740497771672326717479)
        ·
          refine ⟨20294610746657508490076219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13529740497771672326717479 20294610746657508490076219)
          ·
            refine ⟨30441916119986262735114329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20294610746657508490076219 30441916119986262735114329)
            ·
              refine ⟨22831437089989697051335747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30441916119986262735114329 22831437089989697051335747)
              ·
                refine ⟨34247155634984545577003621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22831437089989697051335747 34247155634984545577003621)
                ·
                  refine ⟨6421341681559602295688179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34247155634984545577003621 6421341681559602295688179)
                  ·
                    refine ⟨9632012522339403443532269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6421341681559602295688179 9632012522339403443532269)
                    ·
                      refine ⟨3612004695877276291324601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632012522339403443532269 3612004695877276291324601)
                      ·
                        rfl

theorem cell23_7034354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7034354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034354 prefixEnd_7034354 := by exact prefixLift 7034354
  have htrace : WordTrace (prefixWord ++ tailWord_7034354) baseStart_7034354 baseEnd_7034354 := by
    simpa [prefixWord, tailWord_7034354, baseEnd_7034354] using wordTrace_append hprefix tailTrace_7034354
  have hstable : (prefixWord ++ tailWord_7034354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034354).length < 2 ^ (prefixWord ++ tailWord_7034354).sum := by decide
  have hdescent : baseEnd_7034354 < baseStart_7034354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034377 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 1, 4, 2]
def baseStart_7034377 : Nat := 118140960795 + 7034377 * 2 ^ 59
def prefixEnd_7034377 : Nat := 4983230072969 + 3 ^ 40 * 7034377 * 2
def baseEnd_7034377 : Nat := 3612016505932329701336995

theorem tailTrace_7034377 : CollatzResearch.WordTrace tailWord_7034377 prefixEnd_7034377 3612016505932329701336995 := by
  unfold tailWord_7034377
  simp only [CollatzResearch.WordTrace]
  refine ⟨256564806836660979790285385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171043204557773986526856923 256564806836660979790285385)
  ·
    refine ⟨192423605127495734842714039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256564806836660979790285385 192423605127495734842714039)
    ·
      refine ⟨288635407691243602264071059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192423605127495734842714039 288635407691243602264071059)
      ·
        refine ⟨432953111536865403396106589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288635407691243602264071059 432953111536865403396106589)
        ·
          refine ⟨162357416826324526273539971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432953111536865403396106589 162357416826324526273539971)
          ·
            refine ⟨243536125239486789410309957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162357416826324526273539971 243536125239486789410309957)
            ·
              refine ⟨45663023482403773014433117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243536125239486789410309957 45663023482403773014433117)
              ·
                refine ⟨17123633805901414880412419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45663023482403773014433117 17123633805901414880412419)
                ·
                  refine ⟨25685450708852122320618629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17123633805901414880412419 25685450708852122320618629)
                  ·
                    refine ⟨4816022007909772935115993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25685450708852122320618629 4816022007909772935115993)
                    ·
                      refine ⟨3612016505932329701336995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816022007909772935115993 3612016505932329701336995)
                      ·
                        rfl

theorem cell23_7034377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4, 2].length) (baseStart_7034377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034377 prefixEnd_7034377 := by exact prefixLift 7034377
  have htrace : WordTrace (prefixWord ++ tailWord_7034377) baseStart_7034377 baseEnd_7034377 := by
    simpa [prefixWord, tailWord_7034377, baseEnd_7034377] using wordTrace_append hprefix tailTrace_7034377
  have hstable : (prefixWord ++ tailWord_7034377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034377).length < 2 ^ (prefixWord ++ tailWord_7034377).sum := by decide
  have hdescent : baseEnd_7034377 < baseStart_7034377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034437 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_7034437 : Nat := 118140960795 + 7034437 * 2 ^ 59
def prefixEnd_7034437 : Nat := 4983230072969 + 3 ^ 40 * 7034437 * 2
def baseEnd_7034437 : Nat := 3612047314771599466586719

theorem tailTrace_7034437 : CollatzResearch.WordTrace tailWord_7034437 prefixEnd_7034437 3612047314771599466586719 := by
  unfold tailWord_7034437
  simp only [CollatzResearch.WordTrace]
  refine ⟨256566995216443610037469565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171044663477629073358313043 256566995216443610037469565)
  ·
    refine ⟨96212623206166353764051087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256566995216443610037469565 96212623206166353764051087)
    ·
      refine ⟨144318934809249530646076631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96212623206166353764051087 144318934809249530646076631)
      ·
        refine ⟨216478402213874295969114947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144318934809249530646076631 216478402213874295969114947)
        ·
          refine ⟨324717603320811443953672421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216478402213874295969114947 324717603320811443953672421)
          ·
            refine ⟨60884550622652145741313579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324717603320811443953672421 60884550622652145741313579)
            ·
              refine ⟨91326825933978218611970369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60884550622652145741313579 91326825933978218611970369)
              ·
                refine ⟨68495119450483663958977777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91326825933978218611970369 68495119450483663958977777)
                ·
                  refine ⟨51371339587862747969233333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68495119450483663958977777 51371339587862747969233333)
                  ·
                    refine ⟨4816063086362132622115625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51371339587862747969233333 4816063086362132622115625)
                    ·
                      refine ⟨3612047314771599466586719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816063086362132622115625 3612047314771599466586719)
                      ·
                        rfl

theorem cell23_7034437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_7034437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034437 prefixEnd_7034437 := by exact prefixLift 7034437
  have htrace : WordTrace (prefixWord ++ tailWord_7034437) baseStart_7034437 baseEnd_7034437 := by
    simpa [prefixWord, tailWord_7034437, baseEnd_7034437] using wordTrace_append hprefix tailTrace_7034437
  have hstable : (prefixWord ++ tailWord_7034437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034437).length < 2 ^ (prefixWord ++ tailWord_7034437).sum := by decide
  have hdescent : baseEnd_7034437 < baseStart_7034437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034528 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 1, 4]
def baseStart_7034528 : Nat := 118140960795 + 7034528 * 2 ^ 59
def prefixEnd_7034528 : Nat := 4983230072969 + 3 ^ 40 * 7034528 * 2
def baseEnd_7034528 : Nat := 1204031347170386203516267

theorem tailTrace_7034528 : CollatzResearch.WordTrace tailWord_7034528 prefixEnd_7034528 1204031347170386203516267 := by
  unfold tailWord_7034528
  simp only [CollatzResearch.WordTrace]
  refine ⟨128285157129556966289516119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171046876172742621719354825 128285157129556966289516119)
  ·
    refine ⟨192427735694335449434274179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128285157129556966289516119 192427735694335449434274179)
    ·
      refine ⟨288641603541503174151411269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192427735694335449434274179 288641603541503174151411269)
      ·
        refine ⟨54120300664031845153389613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288641603541503174151411269 54120300664031845153389613)
        ·
          refine ⟨20295112749011941932521105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54120300664031845153389613 20295112749011941932521105)
          ·
            refine ⟨15221334561758956449390829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20295112749011941932521105 15221334561758956449390829)
            ·
              refine ⟨5708000460659608668521561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15221334561758956449390829 5708000460659608668521561)
              ·
                refine ⟨4281000345494706501391171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708000460659608668521561 4281000345494706501391171)
                ·
                  refine ⟨6421500518242059752086757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281000345494706501391171 6421500518242059752086757)
                  ·
                    refine ⟨1204031347170386203516267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421500518242059752086757 1204031347170386203516267)
                    ·
                      rfl

theorem cell23_7034528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 4].length) (baseStart_7034528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034528 prefixEnd_7034528 := by exact prefixLift 7034528
  have htrace : WordTrace (prefixWord ++ tailWord_7034528) baseStart_7034528 baseEnd_7034528 := by
    simpa [prefixWord, tailWord_7034528, baseEnd_7034528] using wordTrace_append hprefix tailTrace_7034528
  have hstable : (prefixWord ++ tailWord_7034528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034528).length < 2 ^ (prefixWord ++ tailWord_7034528).sum := by decide
  have hdescent : baseEnd_7034528 < baseStart_7034528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034540 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_7034540 : Nat := 118140960795 + 7034540 * 2 ^ 59
def prefixEnd_7034540 : Nat := 4983230072969 + 3 ^ 40 * 7034540 * 2
def baseEnd_7034540 : Nat := 3612100203279012563598745

theorem tailTrace_7034540 : CollatzResearch.WordTrace tailWord_7034540 prefixEnd_7034540 3612100203279012563598745 := by
  unfold tailWord_7034540
  simp only [CollatzResearch.WordTrace]
  refine ⟨128285375967535229314234537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171047167956713639085646049 128285375967535229314234537)
  ·
    refine ⟨96214031975651421985675903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128285375967535229314234537 96214031975651421985675903)
    ·
      refine ⟨144321047963477132978513855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96214031975651421985675903 144321047963477132978513855)
      ·
        refine ⟨216481571945215699467770783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144321047963477132978513855 216481571945215699467770783)
        ·
          refine ⟨324722357917823549201656175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216481571945215699467770783 324722357917823549201656175)
          ·
            refine ⟨487083536876735323802484263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324722357917823549201656175 487083536876735323802484263)
            ·
              refine ⟨730625305315102985703726395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487083536876735323802484263 730625305315102985703726395)
              ·
                refine ⟨1095937957972654478555589593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730625305315102985703726395 1095937957972654478555589593)
                ·
                  refine ⟨821953468479490858916692195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095937957972654478555589593 821953468479490858916692195)
                  ·
                    refine ⟨1232930202719236288375038293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821953468479490858916692195 1232930202719236288375038293)
                    ·
                      refine ⟨3612100203279012563598745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1232930202719236288375038293 3612100203279012563598745)
                      ·
                        rfl

theorem cell23_7034540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_7034540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034540 prefixEnd_7034540 := by exact prefixLift 7034540
  have htrace : WordTrace (prefixWord ++ tailWord_7034540) baseStart_7034540 baseEnd_7034540 := by
    simpa [prefixWord, tailWord_7034540, baseEnd_7034540] using wordTrace_append hprefix tailTrace_7034540
  have hstable : (prefixWord ++ tailWord_7034540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034540).length < 2 ^ (prefixWord ++ tailWord_7034540).sum := by decide
  have hdescent : baseEnd_7034540 < baseStart_7034540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034554 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_7034554 : Nat := 118140960795 + 7034554 * 2 ^ 59
def prefixEnd_7034554 : Nat := 4983230072969 + 3 ^ 40 * 7034554 * 2
def baseEnd_7034554 : Nat := 1204035797336058502941227

theorem tailTrace_7034554 : CollatzResearch.WordTrace tailWord_7034554 prefixEnd_7034554 1204035797336058502941227 := by
  unfold tailWord_7034554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64142815639254934754869679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171047508371346492679652477 64142815639254934754869679)
  ·
    refine ⟨96214223458882402132304519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64142815639254934754869679 96214223458882402132304519)
    ·
      refine ⟨144321335188323603198456779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96214223458882402132304519 144321335188323603198456779)
      ·
        refine ⟨216482002782485404797685169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144321335188323603198456779 216482002782485404797685169)
        ·
          refine ⟨162361502086864053598263877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216482002782485404797685169 162361502086864053598263877)
          ·
            refine ⟨30442781641287010049674477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162361502086864053598263877 30442781641287010049674477)
            ·
              refine ⟨11416043115482628768627929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30442781641287010049674477 11416043115482628768627929)
              ·
                refine ⟨8562032336611971576470947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11416043115482628768627929 8562032336611971576470947)
                ·
                  refine ⟨12843048504917957364706421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562032336611971576470947 12843048504917957364706421)
                  ·
                    refine ⟨1204035797336058502941227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12843048504917957364706421 1204035797336058502941227)
                    ·
                      rfl

theorem cell23_7034554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_7034554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034554 prefixEnd_7034554 := by exact prefixLift 7034554
  have htrace : WordTrace (prefixWord ++ tailWord_7034554) baseStart_7034554 baseEnd_7034554 := by
    simpa [prefixWord, tailWord_7034554, baseEnd_7034554] using wordTrace_append hprefix tailTrace_7034554
  have hstable : (prefixWord ++ tailWord_7034554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034554).length < 2 ^ (prefixWord ++ tailWord_7034554).sum := by decide
  have hdescent : baseEnd_7034554 < baseStart_7034554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034567 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 1, 6]
def baseStart_7034567 : Nat := 118140960795 + 7034567 * 2 ^ 59
def prefixEnd_7034567 : Nat := 4983230072969 + 3 ^ 40 * 7034567 * 2
def baseEnd_7034567 : Nat := 1204038022418894652653707

theorem tailTrace_7034567 : CollatzResearch.WordTrace tailWord_7034567 prefixEnd_7034567 1204038022418894652653707 := by
  unfold tailWord_7034567
  simp only [CollatzResearch.WordTrace]
  refine ⟨256571736705972642239701955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171047824470648428159801303 256571736705972642239701955)
  ·
    refine ⟨384857605058958963359552933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256571736705972642239701955 384857605058958963359552933)
    ·
      refine ⟨72160800948554805629916175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384857605058958963359552933 72160800948554805629916175)
      ·
        refine ⟨108241201422832208444874263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72160800948554805629916175 108241201422832208444874263)
        ·
          refine ⟨162361802134248312667311395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108241201422832208444874263 162361802134248312667311395)
          ·
            refine ⟨243542703201372469000967093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162361802134248312667311395 243542703201372469000967093)
            ·
              refine ⟨22832128425128668968840665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243542703201372469000967093 22832128425128668968840665)
              ·
                refine ⟨17124096318846501726630499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22832128425128668968840665 17124096318846501726630499)
                ·
                  refine ⟨25686144478269752589945749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17124096318846501726630499 25686144478269752589945749)
                  ·
                    refine ⟨1204038022418894652653707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25686144478269752589945749 1204038022418894652653707)
                    ·
                      rfl

theorem cell23_7034567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_7034567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034567 prefixEnd_7034567 := by exact prefixLift 7034567
  have htrace : WordTrace (prefixWord ++ tailWord_7034567) baseStart_7034567 baseEnd_7034567 := by
    simpa [prefixWord, tailWord_7034567, baseEnd_7034567] using wordTrace_append hprefix tailTrace_7034567
  have hstable : (prefixWord ++ tailWord_7034567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034567).length < 2 ^ (prefixWord ++ tailWord_7034567).sum := by decide
  have hdescent : baseEnd_7034567 < baseStart_7034567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034585 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 1, 1, 3]
def baseStart_7034585 : Nat := 118140960795 + 7034585 * 2 ^ 59
def prefixEnd_7034585 : Nat := 4983230072969 + 3 ^ 40 * 7034585 * 2
def baseEnd_7034585 : Nat := 3612123309908464887536039

theorem tailTrace_7034585 : CollatzResearch.WordTrace tailWord_7034585 prefixEnd_7034585 3612123309908464887536039 := by
  unfold tailWord_7034585
  simp only [CollatzResearch.WordTrace]
  refine ⟨256572393219907431313857209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171048262146604954209238139 256572393219907431313857209)
  ·
    refine ⟨192429294914930573485392907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256572393219907431313857209 192429294914930573485392907)
    ·
      refine ⟨288643942372395860228089361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192429294914930573485392907 288643942372395860228089361)
      ·
        refine ⟨216482956779296895171067021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288643942372395860228089361 216482956779296895171067021)
        ·
          refine ⟨81181108792236335689150133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216482956779296895171067021 81181108792236335689150133)
          ·
            refine ⟨7610728949272156470857825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81181108792236335689150133 7610728949272156470857825)
            ·
              refine ⟨5708046711954117353143369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610728949272156470857825 5708046711954117353143369)
              ·
                refine ⟨4281035033965588014857527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708046711954117353143369 4281035033965588014857527)
                ·
                  refine ⟨6421552550948382022286291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281035033965588014857527 6421552550948382022286291)
                  ·
                    refine ⟨9632328826422573033429437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6421552550948382022286291 9632328826422573033429437)
                    ·
                      refine ⟨3612123309908464887536039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632328826422573033429437 3612123309908464887536039)
                      ·
                        rfl

theorem cell23_7034585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_7034585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034585 prefixEnd_7034585 := by exact prefixLift 7034585
  have htrace : WordTrace (prefixWord ++ tailWord_7034585) baseStart_7034585 baseEnd_7034585 := by
    simpa [prefixWord, tailWord_7034585, baseEnd_7034585] using wordTrace_append hprefix tailTrace_7034585
  have hstable : (prefixWord ++ tailWord_7034585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034585).length < 2 ^ (prefixWord ++ tailWord_7034585).sum := by decide
  have hdescent : baseEnd_7034585 < baseStart_7034585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034591 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 3, 2, 2]
def baseStart_7034591 : Nat := 118140960795 + 7034591 * 2 ^ 59
def prefixEnd_7034591 : Nat := 4983230072969 + 3 ^ 40 * 7034591 * 2
def baseEnd_7034591 : Nat := 3612126390792391864061011

theorem tailTrace_7034591 : CollatzResearch.WordTrace tailWord_7034591 prefixEnd_7034591 3612126390792391864061011 := by
  unfold tailWord_7034591
  simp only [CollatzResearch.WordTrace]
  refine ⟨256572612057885694338575627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171048408038590462892383751 256572612057885694338575627)
  ·
    refine ⟨384858918086828541507863441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256572612057885694338575627 384858918086828541507863441)
    ·
      refine ⟨288644188565121406130897581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384858918086828541507863441 288644188565121406130897581)
      ·
        refine ⟨108241570711920527299086593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288644188565121406130897581 108241570711920527299086593)
        ·
          refine ⟨81181178033940395474314945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108241570711920527299086593 81181178033940395474314945)
          ·
            refine ⟨60885883525455296605736209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81181178033940395474314945 60885883525455296605736209)
            ·
              refine ⟨45664412644091472454302157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60885883525455296605736209 45664412644091472454302157)
              ·
                refine ⟨17124154741534302170363309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45664412644091472454302157 17124154741534302170363309)
                ·
                  refine ⟨6421558028075363313886241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17124154741534302170363309 6421558028075363313886241)
                  ·
                    refine ⟨4816168521056522485414681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421558028075363313886241 4816168521056522485414681)
                    ·
                      refine ⟨3612126390792391864061011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816168521056522485414681 3612126390792391864061011)
                      ·
                        rfl

theorem cell23_7034591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_7034591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034591 prefixEnd_7034591 := by exact prefixLift 7034591
  have htrace : WordTrace (prefixWord ++ tailWord_7034591) baseStart_7034591 baseEnd_7034591 := by
    simpa [prefixWord, tailWord_7034591, baseEnd_7034591] using wordTrace_append hprefix tailTrace_7034591
  have hstable : (prefixWord ++ tailWord_7034591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034591).length < 2 ^ (prefixWord ++ tailWord_7034591).sum := by decide
  have hdescent : baseEnd_7034591 < baseStart_7034591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034612 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7034612 : Nat := 118140960795 + 7034612 * 2 ^ 59
def prefixEnd_7034612 : Nat := 4983230072969 + 3 ^ 40 * 7034612 * 2
def baseEnd_7034612 : Nat := 3612137173886136281898415

theorem tailTrace_7034612 : CollatzResearch.WordTrace tailWord_7034612 prefixEnd_7034612 3612137173886136281898415 := by
  unfold tailWord_7034612
  simp only [CollatzResearch.WordTrace]
  refine ⟨128286688995404807462545045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171048918660539743283393393 128286688995404807462545045)
  ·
    refine ⟨6013438546659600349806799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128286688995404807462545045 6013438546659600349806799)
    ·
      refine ⟨9020157819989400524710199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013438546659600349806799 9020157819989400524710199)
      ·
        refine ⟨13530236729984100787065299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020157819989400524710199 13530236729984100787065299)
        ·
          refine ⟨20295355094976151180597949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530236729984100787065299 20295355094976151180597949)
          ·
            refine ⟨7610758160616056692724231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20295355094976151180597949 7610758160616056692724231)
            ·
              refine ⟨11416137240924085039086347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610758160616056692724231 11416137240924085039086347)
              ·
                refine ⟨17124205861386127558629521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11416137240924085039086347 17124205861386127558629521)
                ·
                  refine ⟨12843154396039595668972141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17124205861386127558629521 12843154396039595668972141)
                  ·
                    refine ⟨4816182898514848375864553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12843154396039595668972141 4816182898514848375864553)
                    ·
                      refine ⟨3612137173886136281898415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816182898514848375864553 3612137173886136281898415)
                      ·
                        rfl

theorem cell23_7034612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7034612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034612 prefixEnd_7034612 := by exact prefixLift 7034612
  have htrace : WordTrace (prefixWord ++ tailWord_7034612) baseStart_7034612 baseEnd_7034612 := by
    simpa [prefixWord, tailWord_7034612, baseEnd_7034612] using wordTrace_append hprefix tailTrace_7034612
  have hstable : (prefixWord ++ tailWord_7034612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034612).length < 2 ^ (prefixWord ++ tailWord_7034612).sum := by decide
  have hdescent : baseEnd_7034612 < baseStart_7034612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034624 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3]
def baseStart_7034624 : Nat := 118140960795 + 7034624 * 2 ^ 59
def prefixEnd_7034624 : Nat := 4983230072969 + 3 ^ 40 * 7034624 * 2
def baseEnd_7034624 : Nat := 3612143335653990234948359

theorem tailTrace_7034624 : CollatzResearch.WordTrace tailWord_7034624 prefixEnd_7034624 3612143335653990234948359 := by
  unfold tailWord_7034624
  simp only [CollatzResearch.WordTrace]
  refine ⟨128286907833383070487263463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171049210444510760649684617 128286907833383070487263463)
  ·
    refine ⟨192430361750074605730895195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128286907833383070487263463 192430361750074605730895195)
    ·
      refine ⟨288645542625111908596342793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192430361750074605730895195 288645542625111908596342793)
      ·
        refine ⟨216484156968833931447257095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288645542625111908596342793 216484156968833931447257095)
        ·
          refine ⟨324726235453250897170885643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216484156968833931447257095 324726235453250897170885643)
          ·
            refine ⟨487089353179876345756328465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324726235453250897170885643 487089353179876345756328465)
            ·
              refine ⟨365317014884907259317246349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487089353179876345756328465 365317014884907259317246349)
              ·
                refine ⟨136993880581840222243967381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365317014884907259317246349 136993880581840222243967381)
                ·
                  refine ⟨6421588152273760417685971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136993880581840222243967381 6421588152273760417685971)
                  ·
                    refine ⟨9632382228410640626528957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6421588152273760417685971 9632382228410640626528957)
                    ·
                      refine ⟨3612143335653990234948359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632382228410640626528957 3612143335653990234948359)
                      ·
                        rfl

theorem cell23_7034624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_7034624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034624 prefixEnd_7034624 := by exact prefixLift 7034624
  have htrace : WordTrace (prefixWord ++ tailWord_7034624) baseStart_7034624 baseEnd_7034624 := by
    simpa [prefixWord, tailWord_7034624, baseEnd_7034624] using wordTrace_append hprefix tailTrace_7034624
  have hstable : (prefixWord ++ tailWord_7034624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034624).length < 2 ^ (prefixWord ++ tailWord_7034624).sum := by decide
  have hdescent : baseEnd_7034624 < baseStart_7034624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034628 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7034628 : Nat := 118140960795 + 7034628 * 2 ^ 59
def prefixEnd_7034628 : Nat := 4983230072969 + 3 ^ 40 * 7034628 * 2
def baseEnd_7034628 : Nat := 3612145389576608219298341

theorem tailTrace_7034628 : CollatzResearch.WordTrace tailWord_7034628 prefixEnd_7034628 3612145389576608219298341 := by
  unfold tailWord_7034628
  simp only [CollatzResearch.WordTrace]
  refine ⟨128286980779375824828836269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171049307705834433105115025 128286980779375824828836269)
  ·
    refine ⟨48107617792265934310813601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128286980779375824828836269 48107617792265934310813601)
    ·
      refine ⟨36080713344199450733110201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48107617792265934310813601 36080713344199450733110201)
      ·
        refine ⟨27060535008149588049832651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36080713344199450733110201 27060535008149588049832651)
        ·
          refine ⟨40590802512224382074748977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27060535008149588049832651 40590802512224382074748977)
          ·
            refine ⟨30443101884168286556061733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40590802512224382074748977 30443101884168286556061733)
            ·
              refine ⟨5708081603281553729261575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30443101884168286556061733 5708081603281553729261575)
              ·
                refine ⟨8562122404922330593892363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708081603281553729261575 8562122404922330593892363)
                ·
                  refine ⟨12843183607383495890838545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562122404922330593892363 12843183607383495890838545)
                  ·
                    refine ⟨9632387705537621918128909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12843183607383495890838545 9632387705537621918128909)
                    ·
                      refine ⟨3612145389576608219298341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632387705537621918128909 3612145389576608219298341)
                      ·
                        rfl

theorem cell23_7034628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7034628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034628 prefixEnd_7034628 := by exact prefixLift 7034628
  have htrace : WordTrace (prefixWord ++ tailWord_7034628) baseStart_7034628 baseEnd_7034628 := by
    simpa [prefixWord, tailWord_7034628, baseEnd_7034628] using wordTrace_append hprefix tailTrace_7034628
  have hstable : (prefixWord ++ tailWord_7034628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034628).length < 2 ^ (prefixWord ++ tailWord_7034628).sum := by decide
  have hdescent : baseEnd_7034628 < baseStart_7034628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034642 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7034642 : Nat := 118140960795 + 7034642 * 2 ^ 59
def prefixEnd_7034642 : Nat := 4983230072969 + 3 ^ 40 * 7034642 * 2
def baseEnd_7034642 : Nat := 3612152578305771164523277

theorem tailTrace_7034642 : CollatzResearch.WordTrace tailWord_7034642 prefixEnd_7034642 3612152578305771164523277 := by
  unfold tailWord_7034642
  simp only [CollatzResearch.WordTrace]
  refine ⟨64143618045175232512170545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171049648120467286699121453 64143618045175232512170545)
  ·
    refine ⟨48107713533881424384127909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64143618045175232512170545 48107713533881424384127909)
    ·
      refine ⟨9020196287602767072023983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48107713533881424384127909 9020196287602767072023983)
      ·
        refine ⟨13530294431404150608035975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020196287602767072023983 13530294431404150608035975)
        ·
          refine ⟨20295441647106225912053963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530294431404150608035975 20295441647106225912053963)
          ·
            refine ⟨30443162470659338868080945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20295441647106225912053963 30443162470659338868080945)
            ·
              refine ⟨22832371852994504151060709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30443162470659338868080945 22832371852994504151060709)
              ·
                refine ⟨4281069722436469528323883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22832371852994504151060709 4281069722436469528323883)
                ·
                  refine ⟨6421604583654704292485825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281069722436469528323883 6421604583654704292485825)
                  ·
                    refine ⟨4816203437741028219364369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421604583654704292485825 4816203437741028219364369)
                    ·
                      refine ⟨3612152578305771164523277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816203437741028219364369 3612152578305771164523277)
                      ·
                        rfl

theorem cell23_7034642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7034642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034642 prefixEnd_7034642 := by exact prefixLift 7034642
  have htrace : WordTrace (prefixWord ++ tailWord_7034642) baseStart_7034642 baseEnd_7034642 := by
    simpa [prefixWord, tailWord_7034642, baseEnd_7034642] using wordTrace_append hprefix tailTrace_7034642
  have hstable : (prefixWord ++ tailWord_7034642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034642).length < 2 ^ (prefixWord ++ tailWord_7034642).sum := by decide
  have hdescent : baseEnd_7034642 < baseStart_7034642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034668 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_7034668 : Nat := 118140960795 + 7034668 * 2 ^ 59
def prefixEnd_7034668 : Nat := 4983230072969 + 3 ^ 40 * 7034668 * 2
def baseEnd_7034668 : Nat := 3612165928802788062798157

theorem tailTrace_7034668 : CollatzResearch.WordTrace tailWord_7034668 prefixEnd_7034668 3612165928802788062798157 := by
  unfold tailWord_7034668
  simp only [CollatzResearch.WordTrace]
  refine ⟨128287710239303368244564329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171050280319071157659419105 128287710239303368244564329)
  ·
    refine ⟨96215782679477526183423247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128287710239303368244564329 96215782679477526183423247)
    ·
      refine ⟨144323674019216289275134871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96215782679477526183423247 144323674019216289275134871)
      ·
        refine ⟨216485511028824433912702307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144323674019216289275134871 216485511028824433912702307)
        ·
          refine ⟨324728266543236650869053461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216485511028824433912702307 324728266543236650869053461)
          ·
            refine ⟨15221637494214218009486881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324728266543236650869053461 15221637494214218009486881)
            ·
              refine ⟨11416228120660663507115161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15221637494214218009486881 11416228120660663507115161)
              ·
                refine ⟨8562171090495497630336371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11416228120660663507115161 8562171090495497630336371)
                ·
                  refine ⟨12843256635743246445504557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562171090495497630336371 12843256635743246445504557)
                  ·
                    refine ⟨4816221238403717417064209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12843256635743246445504557 4816221238403717417064209)
                    ·
                      refine ⟨3612165928802788062798157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816221238403717417064209 3612165928802788062798157)
                      ·
                        rfl

theorem cell23_7034668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_7034668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034668 prefixEnd_7034668 := by exact prefixLift 7034668
  have htrace : WordTrace (prefixWord ++ tailWord_7034668) baseStart_7034668 baseEnd_7034668 := by
    simpa [prefixWord, tailWord_7034668, baseEnd_7034668] using wordTrace_append hprefix tailTrace_7034668
  have hstable : (prefixWord ++ tailWord_7034668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034668).length < 2 ^ (prefixWord ++ tailWord_7034668).sum := by decide
  have hdescent : baseEnd_7034668 < baseStart_7034668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034697 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_7034697 : Nat := 118140960795 + 7034697 * 2 ^ 59
def prefixEnd_7034697 : Nat := 4983230072969 + 3 ^ 40 * 7034697 * 2
def baseEnd_7034697 : Nat := 3612180819741768449335523

theorem tailTrace_7034697 : CollatzResearch.WordTrace tailWord_7034697 prefixEnd_7034697 3612180819741768449335523 := by
  unfold tailWord_7034697
  simp only [CollatzResearch.WordTrace]
  refine ⟨256576478195501674441934345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171050985463667782961289563 256576478195501674441934345)
  ·
    refine ⟨192432358646626255831450759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256576478195501674441934345 192432358646626255831450759)
    ·
      refine ⟨288648537969939383747176139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192432358646626255831450759 288648537969939383747176139)
      ·
        refine ⟨432972806954909075620764209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288648537969939383747176139 432972806954909075620764209)
        ·
          refine ⟨324729605216181806715573157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432972806954909075620764209 324729605216181806715573157)
          ·
            refine ⟨60886800978034088759169967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324729605216181806715573157 60886800978034088759169967)
            ·
              refine ⟨91330201467051133138754951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60886800978034088759169967 91330201467051133138754951)
              ·
                refine ⟨136995302200576699708132427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91330201467051133138754951 136995302200576699708132427)
                ·
                  refine ⟨205492953300865049562198641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136995302200576699708132427 205492953300865049562198641)
                  ·
                    refine ⟨154119714975648787171648981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205492953300865049562198641 154119714975648787171648981)
                    ·
                      refine ⟨3612180819741768449335523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154119714975648787171648981 3612180819741768449335523)
                      ·
                        rfl

theorem cell23_7034697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_7034697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034697 prefixEnd_7034697 := by exact prefixLift 7034697
  have htrace : WordTrace (prefixWord ++ tailWord_7034697) baseStart_7034697 baseEnd_7034697 := by
    simpa [prefixWord, tailWord_7034697, baseEnd_7034697] using wordTrace_append hprefix tailTrace_7034697
  have hstable : (prefixWord ++ tailWord_7034697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034697).length < 2 ^ (prefixWord ++ tailWord_7034697).sum := by decide
  have hdescent : baseEnd_7034697 < baseStart_7034697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034698 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_7034698 : Nat := 118140960795 + 7034698 * 2 ^ 59
def prefixEnd_7034698 : Nat := 4983230072969 + 3 ^ 40 * 7034698 * 2
def baseEnd_7034698 : Nat := 3612181333222422945423019

theorem tailTrace_7034698 : CollatzResearch.WordTrace tailWord_7034698 prefixEnd_7034698 3612181333222422945423019 := by
  unfold tailWord_7034698
  simp only [CollatzResearch.WordTrace]
  refine ⟨64144128667124512903180187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171051009778998701075147165 64144128667124512903180187)
  ·
    refine ⟨96216193000686769354770281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64144128667124512903180187 96216193000686769354770281)
    ·
      refine ⟨72162144750515077016077711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96216193000686769354770281 72162144750515077016077711)
      ·
        refine ⟨108243217125772615524116567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72162144750515077016077711 108243217125772615524116567)
        ·
          refine ⟨162364825688658923286174851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108243217125772615524116567 162364825688658923286174851)
          ·
            refine ⟨243547238532988384929262277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162364825688658923286174851 243547238532988384929262277)
            ·
              refine ⟨45665107224935322174236677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243547238532988384929262277 45665107224935322174236677)
              ·
                refine ⟨8562207604675372907669377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45665107224935322174236677 8562207604675372907669377)
                ·
                  refine ⟨6421655703506529680752033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8562207604675372907669377 6421655703506529680752033)
                  ·
                    refine ⟨4816241777629897260564025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421655703506529680752033 4816241777629897260564025)
                    ·
                      refine ⟨3612181333222422945423019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816241777629897260564025 3612181333222422945423019)
                      ·
                        rfl

theorem cell23_7034698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_7034698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034698 prefixEnd_7034698 := by exact prefixLift 7034698
  have htrace : WordTrace (prefixWord ++ tailWord_7034698) baseStart_7034698 baseEnd_7034698 := by
    simpa [prefixWord, tailWord_7034698, baseEnd_7034698] using wordTrace_append hprefix tailTrace_7034698
  have hstable : (prefixWord ++ tailWord_7034698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034698).length < 2 ^ (prefixWord ++ tailWord_7034698).sum := by decide
  have hdescent : baseEnd_7034698 < baseStart_7034698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034714 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_7034714 : Nat := 118140960795 + 7034714 * 2 ^ 59
def prefixEnd_7034714 : Nat := 4983230072969 + 3 ^ 40 * 7034714 * 2
def baseEnd_7034714 : Nat := 3612189548912894882822945

theorem tailTrace_7034714 : CollatzResearch.WordTrace tailWord_7034714 prefixEnd_7034714 3612189548912894882822945 := by
  unfold tailWord_7034714
  simp only [CollatzResearch.WordTrace]
  refine ⟨64144274559110021586325799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171051398824293390896868797 64144274559110021586325799)
  ·
    refine ⟨96216411838665032379488699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64144274559110021586325799 96216411838665032379488699)
    ·
      refine ⟨144324617757997548569233049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96216411838665032379488699 144324617757997548569233049)
      ·
        refine ⟨108243463318498161426924787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144324617757997548569233049 108243463318498161426924787)
        ·
          refine ⟨162365194977747242140387181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108243463318498161426924787 162365194977747242140387181)
          ·
            refine ⟨60886948116655215802645193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162365194977747242140387181 60886948116655215802645193)
            ·
              refine ⟨45665211087491411851983895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60886948116655215802645193 45665211087491411851983895)
              ·
                refine ⟨68497816631237117777975843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45665211087491411851983895 68497816631237117777975843)
                ·
                  refine ⟨102746724946855676666963765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68497816631237117777975843 102746724946855676666963765)
                  ·
                    refine ⟨9632505463767719687527853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102746724946855676666963765 9632505463767719687527853)
                    ·
                      refine ⟨3612189548912894882822945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632505463767719687527853 3612189548912894882822945)
                      ·
                        rfl

theorem cell23_7034714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_7034714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034714 prefixEnd_7034714 := by exact prefixLift 7034714
  have htrace : WordTrace (prefixWord ++ tailWord_7034714) baseStart_7034714 baseEnd_7034714 := by
    simpa [prefixWord, tailWord_7034714, baseEnd_7034714] using wordTrace_append hprefix tailTrace_7034714
  have hstable : (prefixWord ++ tailWord_7034714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034714).length < 2 ^ (prefixWord ++ tailWord_7034714).sum := by decide
  have hdescent : baseEnd_7034714 < baseStart_7034714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034781 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_7034781 : Nat := 118140960795 + 7034781 * 2 ^ 59
def prefixEnd_7034781 : Nat := 4983230072969 + 3 ^ 40 * 7034781 * 2
def baseEnd_7034781 : Nat := 1204074650705582040228379

theorem tailTrace_7034781 : CollatzResearch.WordTrace tailWord_7034781 prefixEnd_7034781 1204074650705582040228379 := by
  unfold tailWord_7034781
  simp only [CollatzResearch.WordTrace]
  refine ⟨256579541927197356787992197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171053027951464904525328131 256579541927197356787992197)
  ·
    refine ⟨48108664111349504397748537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256579541927197356787992197 48108664111349504397748537)
    ·
      refine ⟨36081498083512128298311403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48108664111349504397748537 36081498083512128298311403)
      ·
        refine ⟨54122247125268192447467105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36081498083512128298311403 54122247125268192447467105)
        ·
          refine ⟨40591685343951144335600329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54122247125268192447467105 40591685343951144335600329)
          ·
            refine ⟨30443764007963358251700247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40591685343951144335600329 30443764007963358251700247)
            ·
              refine ⟨45665646011945037377550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30443764007963358251700247 45665646011945037377550371)
              ·
                refine ⟨68498469017917556066325557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45665646011945037377550371 68498469017917556066325557)
                ·
                  refine ⟨6421731470429770881218021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68498469017917556066325557 6421731470429770881218021)
                  ·
                    refine ⟨1204074650705582040228379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421731470429770881218021 1204074650705582040228379)
                    ·
                      rfl

theorem cell23_7034781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_7034781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034781 prefixEnd_7034781 := by exact prefixLift 7034781
  have htrace : WordTrace (prefixWord ++ tailWord_7034781) baseStart_7034781 baseEnd_7034781 := by
    simpa [prefixWord, tailWord_7034781, baseEnd_7034781] using wordTrace_append hprefix tailTrace_7034781
  have hstable : (prefixWord ++ tailWord_7034781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034781).length < 2 ^ (prefixWord ++ tailWord_7034781).sum := by decide
  have hdescent : baseEnd_7034781 < baseStart_7034781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034785 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 2, 5]
def baseStart_7034785 : Nat := 118140960795 + 7034785 * 2 ^ 59
def prefixEnd_7034785 : Nat := 4983230072969 + 3 ^ 40 * 7034785 * 2
def baseEnd_7034785 : Nat := 1204075335346454701678373

theorem tailTrace_7034785 : CollatzResearch.WordTrace tailWord_7034785 prefixEnd_7034785 1204075335346454701678373 := by
  unfold tailWord_7034785
  simp only [CollatzResearch.WordTrace]
  refine ⟨256579687819182865471137809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171053125212788576980758539 256579687819182865471137809)
  ·
    refine ⟨192434765864387149103353357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256579687819182865471137809 192434765864387149103353357)
    ·
      refine ⟨72163037199145180913757509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192434765864387149103353357 72163037199145180913757509)
      ·
        refine ⟨13530569474839721421329533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72163037199145180913757509 13530569474839721421329533)
        ·
          refine ⟨5073963553064895532998575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13530569474839721421329533 5073963553064895532998575)
          ·
            refine ⟨7610945329597343299497863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073963553064895532998575 7610945329597343299497863)
            ·
              refine ⟨11416417994396014949246795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610945329597343299497863 11416417994396014949246795)
              ·
                refine ⟨17124626991594022423870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11416417994396014949246795 17124626991594022423870193)
                ·
                  refine ⟨12843470243695516817902645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17124626991594022423870193 12843470243695516817902645)
                  ·
                    refine ⟨1204075335346454701678373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12843470243695516817902645 1204075335346454701678373)
                    ·
                      rfl

theorem cell23_7034785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_7034785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034785 prefixEnd_7034785 := by exact prefixLift 7034785
  have htrace : WordTrace (prefixWord ++ tailWord_7034785) baseStart_7034785 baseEnd_7034785 := by
    simpa [prefixWord, tailWord_7034785, baseEnd_7034785] using wordTrace_append hprefix tailTrace_7034785
  have hstable : (prefixWord ++ tailWord_7034785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034785).length < 2 ^ (prefixWord ++ tailWord_7034785).sum := by decide
  have hdescent : baseEnd_7034785 < baseStart_7034785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034788 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_7034788 : Nat := 118140960795 + 7034788 * 2 ^ 59
def prefixEnd_7034788 : Nat := 4983230072969 + 3 ^ 40 * 7034788 * 2
def baseEnd_7034788 : Nat := 3612227546481327593297605

theorem tailTrace_7034788 : CollatzResearch.WordTrace tailWord_7034788 prefixEnd_7034788 3612227546481327593297605 := by
  unfold tailWord_7034788
  simp only [CollatzResearch.WordTrace]
  refine ⟨128289898619085998491748509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171053198158781331322331345 128289898619085998491748509)
  ·
    refine ⟨48108711982157249434405691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128289898619085998491748509 48108711982157249434405691)
    ·
      refine ⟨72163067973235874151608537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48108711982157249434405691 72163067973235874151608537)
      ·
        refine ⟨54122300979926905613706403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72163067973235874151608537 54122300979926905613706403)
        ·
          refine ⟨81183451469890358420559605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54122300979926905613706403 81183451469890358420559605)
          ·
            refine ⟨7610948575302221101927463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81183451469890358420559605 7610948575302221101927463)
            ·
              refine ⟨11416422862953331652891195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610948575302221101927463 11416422862953331652891195)
              ·
                refine ⟨17124634294429997479336793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11416422862953331652891195 17124634294429997479336793)
                ·
                  refine ⟨12843475720822498109502595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17124634294429997479336793 12843475720822498109502595)
                  ·
                    refine ⟨19265213581233747164253893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12843475720822498109502595 19265213581233747164253893)
                    ·
                      refine ⟨3612227546481327593297605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19265213581233747164253893 3612227546481327593297605)
                      ·
                        rfl

theorem cell23_7034788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_7034788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034788 prefixEnd_7034788 := by exact prefixLift 7034788
  have htrace : WordTrace (prefixWord ++ tailWord_7034788) baseStart_7034788 baseEnd_7034788 := by
    simpa [prefixWord, tailWord_7034788, baseEnd_7034788] using wordTrace_append hprefix tailTrace_7034788
  have hstable : (prefixWord ++ tailWord_7034788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034788).length < 2 ^ (prefixWord ++ tailWord_7034788).sum := by decide
  have hdescent : baseEnd_7034788 < baseStart_7034788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034828 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 6]
def baseStart_7034828 : Nat := 118140960795 + 7034828 * 2 ^ 59
def prefixEnd_7034828 : Nat := 4983230072969 + 3 ^ 40 * 7034828 * 2
def baseEnd_7034828 : Nat := 401360898411945270755269

theorem tailTrace_7034828 : CollatzResearch.WordTrace tailWord_7034828 prefixEnd_7034828 401360898411945270755269 := by
  unfold tailWord_7034828
  simp only [CollatzResearch.WordTrace]
  refine ⟨128290628079013541907476569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171054170772018055876635425 128290628079013541907476569)
  ·
    refine ⟨96217971059260156430607427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128290628079013541907476569 96217971059260156430607427)
    ·
      refine ⟨144326956588890234645911141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96217971059260156430607427 144326956588890234645911141)
      ·
        refine ⟨27061304360416918996108339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144326956588890234645911141 27061304360416918996108339)
        ·
          refine ⟨40591956540625378494162509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27061304360416918996108339 40591956540625378494162509)
          ·
            refine ⟨15221983702734516935310941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40591956540625378494162509 15221983702734516935310941)
            ·
              refine ⟨5708243888525443850741603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15221983702734516935310941 5708243888525443850741603)
              ·
                refine ⟨8562365832788165776112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708243888525443850741603 8562365832788165776112405)
                ·
                  refine ⟨401360898411945270755269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8562365832788165776112405 401360898411945270755269)
                  ·
                    rfl

theorem cell23_7034828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_7034828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034828 prefixEnd_7034828 := by exact prefixLift 7034828
  have htrace : WordTrace (prefixWord ++ tailWord_7034828) baseStart_7034828 baseEnd_7034828 := by
    simpa [prefixWord, tailWord_7034828, baseEnd_7034828] using wordTrace_append hprefix tailTrace_7034828
  have hstable : (prefixWord ++ tailWord_7034828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034828).length < 2 ^ (prefixWord ++ tailWord_7034828).sum := by decide
  have hdescent : baseEnd_7034828 < baseStart_7034828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034831 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 5, 2]
def baseStart_7034831 : Nat := 118140960795 + 7034831 * 2 ^ 59
def prefixEnd_7034831 : Nat := 4983230072969 + 3 ^ 40 * 7034831 * 2
def baseEnd_7034831 : Nat := 3612249626149470925059907

theorem tailTrace_7034831 : CollatzResearch.WordTrace tailWord_7034831 prefixEnd_7034831 3612249626149470925059907 := by
  unfold tailWord_7034831
  simp only [CollatzResearch.WordTrace]
  refine ⟨256581365577016215327312347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171054243718010810218208231 256581365577016215327312347)
  ·
    refine ⟨384872048365524322990968521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256581365577016215327312347 384872048365524322990968521)
    ·
      refine ⟨288654036274143242243226391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384872048365524322990968521 288654036274143242243226391)
      ·
        refine ⟨432981054411214863364839587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288654036274143242243226391 432981054411214863364839587)
        ·
          refine ⟨649471581616822295047259381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432981054411214863364839587 649471581616822295047259381)
          ·
            refine ⟨60887960776577090160680567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 649471581616822295047259381 60887960776577090160680567)
            ·
              refine ⟨91331941164865635241020851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60887960776577090160680567 91331941164865635241020851)
              ·
                refine ⟨136997911747298452861531277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91331941164865635241020851 136997911747298452861531277)
                ·
                  refine ⟨51374216905236919823074229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136997911747298452861531277 51374216905236919823074229)
                  ·
                    refine ⟨4816332834865961233413209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51374216905236919823074229 4816332834865961233413209)
                    ·
                      refine ⟨3612249626149470925059907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816332834865961233413209 3612249626149470925059907)
                      ·
                        rfl

theorem cell23_7034831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5, 2].length) (baseStart_7034831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034831 prefixEnd_7034831 := by exact prefixLift 7034831
  have htrace : WordTrace (prefixWord ++ tailWord_7034831) baseStart_7034831 baseEnd_7034831 := by
    simpa [prefixWord, tailWord_7034831, baseEnd_7034831] using wordTrace_append hprefix tailTrace_7034831
  have hstable : (prefixWord ++ tailWord_7034831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034831).length < 2 ^ (prefixWord ++ tailWord_7034831).sum := by decide
  have hdescent : baseEnd_7034831 < baseStart_7034831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034865 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_7034865 : Nat := 118140960795 + 7034865 * 2 ^ 59
def prefixEnd_7034865 : Nat := 4983230072969 + 3 ^ 40 * 7034865 * 2
def baseEnd_7034865 : Nat := 3612267084491723792034751

theorem tailTrace_7034865 : CollatzResearch.WordTrace tailWord_7034865 prefixEnd_7034865 3612267084491723792034751 := by
  unfold tailWord_7034865
  simp only [CollatzResearch.WordTrace]
  refine ⟨256582605658893039134050049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171055070439262026089366699 256582605658893039134050049)
  ·
    refine ⟨192436954244169779350537537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256582605658893039134050049 192436954244169779350537537)
    ·
      refine ⟨144327715683127334512903153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192436954244169779350537537 144327715683127334512903153)
      ·
        refine ⟨108245786762345500884677365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144327715683127334512903153 108245786762345500884677365)
        ·
          refine ⟨10148042508969890707938503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108245786762345500884677365 10148042508969890707938503)
          ·
            refine ⟨15222063763454836061907755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10148042508969890707938503 15222063763454836061907755)
            ·
              refine ⟨22833095645182254092861633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222063763454836061907755 22833095645182254092861633)
              ·
                refine ⟨17124821733886690569646225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22833095645182254092861633 17124821733886690569646225)
                ·
                  refine ⟨12843616300415017927234669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17124821733886690569646225 12843616300415017927234669)
                  ·
                    refine ⟨4816356112655631722713001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12843616300415017927234669 4816356112655631722713001)
                    ·
                      refine ⟨3612267084491723792034751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816356112655631722713001 3612267084491723792034751)
                      ·
                        rfl

theorem cell23_7034865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_7034865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034865 prefixEnd_7034865 := by exact prefixLift 7034865
  have htrace : WordTrace (prefixWord ++ tailWord_7034865) baseStart_7034865 baseEnd_7034865 := by
    simpa [prefixWord, tailWord_7034865, baseEnd_7034865] using wordTrace_append hprefix tailTrace_7034865
  have hstable : (prefixWord ++ tailWord_7034865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034865).length < 2 ^ (prefixWord ++ tailWord_7034865).sum := by decide
  have hdescent : baseEnd_7034865 < baseStart_7034865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034881 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7034881 : Nat := 118140960795 + 7034881 * 2 ^ 59
def prefixEnd_7034881 : Nat := 4983230072969 + 3 ^ 40 * 7034881 * 2
def baseEnd_7034881 : Nat := 3612275300182195729434677

theorem tailTrace_7034881 : CollatzResearch.WordTrace tailWord_7034881 prefixEnd_7034881 3612275300182195729434677 := by
  unfold tailWord_7034881
  simp only [CollatzResearch.WordTrace]
  refine ⟨256583189226835073866632497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171055459484556715911088331 256583189226835073866632497)
  ·
    refine ⟨192437391920126305399974373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256583189226835073866632497 192437391920126305399974373)
    ·
      refine ⟨36082010985023682262495195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192437391920126305399974373 36082010985023682262495195)
      ·
        refine ⟨54123016477535523393742793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36082010985023682262495195 54123016477535523393742793)
        ·
          refine ⟨40592262358151642545307095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54123016477535523393742793 40592262358151642545307095)
          ·
            refine ⟨60888393537227463817960643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40592262358151642545307095 60888393537227463817960643)
            ·
              refine ⟨91332590305841195726940965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60888393537227463817960643 91332590305841195726940965)
              ·
                refine ⟨17124860682345224198801431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91332590305841195726940965 17124860682345224198801431)
                ·
                  refine ⟨25687291023517836298202147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17124860682345224198801431 25687291023517836298202147)
                  ·
                    refine ⟨38530936535276754447303221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25687291023517836298202147 38530936535276754447303221)
                    ·
                      refine ⟨3612275300182195729434677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38530936535276754447303221 3612275300182195729434677)
                      ·
                        rfl

theorem cell23_7034881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7034881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034881 prefixEnd_7034881 := by exact prefixLift 7034881
  have htrace : WordTrace (prefixWord ++ tailWord_7034881) baseStart_7034881 baseEnd_7034881 := by
    simpa [prefixWord, tailWord_7034881, baseEnd_7034881] using wordTrace_append hprefix tailTrace_7034881
  have hstable : (prefixWord ++ tailWord_7034881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034881).length < 2 ^ (prefixWord ++ tailWord_7034881).sum := by decide
  have hdescent : baseEnd_7034881 < baseStart_7034881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034888 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_7034888 : Nat := 118140960795 + 7034888 * 2 ^ 59
def prefixEnd_7034888 : Nat := 4983230072969 + 3 ^ 40 * 7034888 * 2
def baseEnd_7034888 : Nat := 1204092964848925734015715

theorem tailTrace_7034888 : CollatzResearch.WordTrace tailWord_7034888 prefixEnd_7034888 1204092964848925734015715 := by
  unfold tailWord_7034888
  simp only [CollatzResearch.WordTrace]
  refine ⟨128291722268904857031068659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171055629691873142708091545 128291722268904857031068659)
  ·
    refine ⟨192437583403357285546602989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128291722268904857031068659 192437583403357285546602989)
    ·
      refine ⟨72164093776258982079976121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192437583403357285546602989 72164093776258982079976121)
      ·
        refine ⟨54123070332194236559982091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72164093776258982079976121 54123070332194236559982091)
        ·
          refine ⟨81184605498291354839973137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54123070332194236559982091 81184605498291354839973137)
          ·
            refine ⟨60888454123718516129979853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81184605498291354839973137 60888454123718516129979853)
            ·
              refine ⟨22833170296394443548742445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60888454123718516129979853 22833170296394443548742445)
              ·
                refine ⟨8562438861147916330778417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22833170296394443548742445 8562438861147916330778417)
                ·
                  refine ⟨6421829145860937248083813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8562438861147916330778417 6421829145860937248083813)
                  ·
                    refine ⟨1204092964848925734015715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421829145860937248083813 1204092964848925734015715)
                    ·
                      rfl

theorem cell23_7034888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_7034888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034888 prefixEnd_7034888 := by exact prefixLift 7034888
  have htrace : WordTrace (prefixWord ++ tailWord_7034888) baseStart_7034888 baseEnd_7034888 := by
    simpa [prefixWord, tailWord_7034888, baseEnd_7034888] using wordTrace_append hprefix tailTrace_7034888
  have hstable : (prefixWord ++ tailWord_7034888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034888).length < 2 ^ (prefixWord ++ tailWord_7034888).sum := by decide
  have hdescent : baseEnd_7034888 < baseStart_7034888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034891 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4]
def baseStart_7034891 : Nat := 118140960795 + 7034891 * 2 ^ 59
def prefixEnd_7034891 : Nat := 4983230072969 + 3 ^ 40 * 7034891 * 2
def baseEnd_7034891 : Nat := 3612280434988740690309631

theorem tailTrace_7034891 : CollatzResearch.WordTrace tailWord_7034891 prefixEnd_7034891 3612280434988740690309631 := by
  unfold tailWord_7034891
  simp only [CollatzResearch.WordTrace]
  refine ⟨256583553956798845574496527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171055702637865897049664351 256583553956798845574496527)
  ·
    refine ⟨384875330935198268361744791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256583553956798845574496527 384875330935198268361744791)
    ·
      refine ⟨577312996402797402542617187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384875330935198268361744791 577312996402797402542617187)
      ·
        refine ⟨865969494604196103813925781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577312996402797402542617187 865969494604196103813925781)
        ·
          refine ⟨40592320059571692366277771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 865969494604196103813925781 40592320059571692366277771)
          ·
            refine ⟨60888480089357538549416657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40592320059571692366277771 60888480089357538549416657)
            ·
              refine ⟨45666360067018153912062493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60888480089357538549416657 45666360067018153912062493)
              ·
                refine ⟨17124885025131807717023435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45666360067018153912062493 17124885025131807717023435)
                ·
                  refine ⟨25687327537697711575535153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17124885025131807717023435 25687327537697711575535153)
                  ·
                    refine ⟨19265495653273283681651365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25687327537697711575535153 19265495653273283681651365)
                    ·
                      refine ⟨3612280434988740690309631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19265495653273283681651365 3612280434988740690309631)
                      ·
                        rfl

theorem cell23_7034891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_7034891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034891 prefixEnd_7034891 := by exact prefixLift 7034891
  have htrace : WordTrace (prefixWord ++ tailWord_7034891) baseStart_7034891 baseEnd_7034891 := by
    simpa [prefixWord, tailWord_7034891, baseEnd_7034891] using wordTrace_append hprefix tailTrace_7034891
  have hstable : (prefixWord ++ tailWord_7034891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034891).length < 2 ^ (prefixWord ++ tailWord_7034891).sum := by decide
  have hdescent : baseEnd_7034891 < baseStart_7034891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034908 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7034908 : Nat := 118140960795 + 7034908 * 2 ^ 59
def prefixEnd_7034908 : Nat := 4983230072969 + 3 ^ 40 * 7034908 * 2
def baseEnd_7034908 : Nat := 3612289164159867123797053

theorem tailTrace_7034908 : CollatzResearch.WordTrace tailWord_7034908 prefixEnd_7034908 3612289164159867123797053 := by
  unfold tailWord_7034908
  simp only [CollatzResearch.WordTrace]
  refine ⟨128292086998868628738932689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171056115998491504985243585 128292086998868628738932689)
  ·
    refine ⟨96219065249151471554199517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128292086998868628738932689 96219065249151471554199517)
    ·
      refine ⟨36082149468431801832824819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96219065249151471554199517 36082149468431801832824819)
      ·
        refine ⟨54123224202647702749237229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36082149468431801832824819 54123224202647702749237229)
        ·
          refine ⟨20296209075992888530963961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54123224202647702749237229 20296209075992888530963961)
          ·
            refine ⟨15222156806994666398222971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20296209075992888530963961 15222156806994666398222971)
            ·
              refine ⟨22833235210491999597334457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222156806994666398222971 22833235210491999597334457)
              ·
                refine ⟨17124926407868999698000843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22833235210491999597334457 17124926407868999698000843)
                ·
                  refine ⟨25687389611803499547001265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17124926407868999698000843 25687389611803499547001265)
                  ·
                    refine ⟨19265542208852624660250949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25687389611803499547001265 19265542208852624660250949)
                    ·
                      refine ⟨3612289164159867123797053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19265542208852624660250949 3612289164159867123797053)
                      ·
                        rfl

theorem cell23_7034908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7034908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034908 prefixEnd_7034908 := by exact prefixLift 7034908
  have htrace : WordTrace (prefixWord ++ tailWord_7034908) baseStart_7034908 baseEnd_7034908 := by
    simpa [prefixWord, tailWord_7034908, baseEnd_7034908] using wordTrace_append hprefix tailTrace_7034908
  have hstable : (prefixWord ++ tailWord_7034908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034908).length < 2 ^ (prefixWord ++ tailWord_7034908).sum := by decide
  have hdescent : baseEnd_7034908 < baseStart_7034908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034915 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 1, 2, 3]
def baseStart_7034915 : Nat := 118140960795 + 7034915 * 2 ^ 59
def prefixEnd_7034915 : Nat := 4983230072969 + 3 ^ 40 * 7034915 * 2
def baseEnd_7034915 : Nat := 3612292758524448596409521

theorem tailTrace_7034915 : CollatzResearch.WordTrace tailWord_7034915 prefixEnd_7034915 3612292758524448596409521 := by
  unfold tailWord_7034915
  simp only [CollatzResearch.WordTrace]
  refine ⟨256584429308711897673370199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171056286205807931782246799 256584429308711897673370199)
  ·
    refine ⟨384876643963067846510055299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256584429308711897673370199 384876643963067846510055299)
    ·
      refine ⟨577314965944601769765082949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384876643963067846510055299 577314965944601769765082949)
      ·
        refine ⟨108246556114612831830953053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 577314965944601769765082949 108246556114612831830953053)
        ·
          refine ⟨40592458542979811936607395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108246556114612831830953053 40592458542979811936607395)
          ·
            refine ⟨60888687814469717904911093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40592458542979811936607395 60888687814469717904911093)
            ·
              refine ⟨5708314482606536053585415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60888687814469717904911093 5708314482606536053585415)
              ·
                refine ⟨8562471723909804080378123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708314482606536053585415 8562471723909804080378123)
                ·
                  refine ⟨12843707585864706120567185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562471723909804080378123 12843707585864706120567185)
                  ·
                    refine ⟨9632780689398529590425389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12843707585864706120567185 9632780689398529590425389)
                    ·
                      refine ⟨3612292758524448596409521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632780689398529590425389 3612292758524448596409521)
                      ·
                        rfl

theorem cell23_7034915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_7034915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034915 prefixEnd_7034915 := by exact prefixLift 7034915
  have htrace : WordTrace (prefixWord ++ tailWord_7034915) baseStart_7034915 baseEnd_7034915 := by
    simpa [prefixWord, tailWord_7034915, baseEnd_7034915] using wordTrace_append hprefix tailTrace_7034915
  have hstable : (prefixWord ++ tailWord_7034915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034915).length < 2 ^ (prefixWord ++ tailWord_7034915).sum := by decide
  have hdescent : baseEnd_7034915 < baseStart_7034915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034929 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 1, 2, 2]
def baseStart_7034929 : Nat := 118140960795 + 7034929 * 2 ^ 59
def prefixEnd_7034929 : Nat := 4983230072969 + 3 ^ 40 * 7034929 * 2
def baseEnd_7034929 : Nat := 3612299947253611541634457

theorem tailTrace_7034929 : CollatzResearch.WordTrace tailWord_7034929 prefixEnd_7034929 3612299947253611541634457 := by
  unfold tailWord_7034929
  simp only [CollatzResearch.WordTrace]
  refine ⟨256584939930661178064379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171056626620440785376253227 256584939930661178064379841)
  ·
    refine ⟨192438704947995883548284881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256584939930661178064379841 192438704947995883548284881)
    ·
      refine ⟨144329028710996912661213661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192438704947995883548284881 144329028710996912661213661)
      ·
        refine ⟨54123385766623842247955123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144329028710996912661213661 54123385766623842247955123)
        ·
          refine ⟨81185078649935763371932685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54123385766623842247955123 81185078649935763371932685)
          ·
            refine ⟨30444404493725911264474757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81185078649935763371932685 30444404493725911264474757)
            ·
              refine ⟨5708325842573608362089017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30444404493725911264474757 5708325842573608362089017)
              ·
                refine ⟨4281244381930206271566763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708325842573608362089017 4281244381930206271566763)
                ·
                  refine ⟨6421866572895309407350145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281244381930206271566763 6421866572895309407350145)
                  ·
                    refine ⟨4816399929671482055512609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421866572895309407350145 4816399929671482055512609)
                    ·
                      refine ⟨3612299947253611541634457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816399929671482055512609 3612299947253611541634457)
                      ·
                        rfl

theorem cell23_7034929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_7034929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034929 prefixEnd_7034929 := by exact prefixLift 7034929
  have htrace : WordTrace (prefixWord ++ tailWord_7034929) baseStart_7034929 baseEnd_7034929 := by
    simpa [prefixWord, tailWord_7034929, baseEnd_7034929] using wordTrace_append hprefix tailTrace_7034929
  have hstable : (prefixWord ++ tailWord_7034929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034929).length < 2 ^ (prefixWord ++ tailWord_7034929).sum := by decide
  have hdescent : baseEnd_7034929 < baseStart_7034929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034945 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7034945 : Nat := 118140960795 + 7034945 * 2 ^ 59
def prefixEnd_7034945 : Nat := 4983230072969 + 3 ^ 40 * 7034945 * 2
def baseEnd_7034945 : Nat := 3612308162944083479034383

theorem tailTrace_7034945 : CollatzResearch.WordTrace tailWord_7034945 prefixEnd_7034945 3612308162944083479034383 := by
  unfold tailWord_7034945
  simp only [CollatzResearch.WordTrace]
  refine ⟨256585523498603212796962289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171057015665735475197974859 256585523498603212796962289)
  ·
    refine ⟨192439142623952409597721717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256585523498603212796962289 192439142623952409597721717)
    ·
      refine ⟨18041169620995538399786411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192439142623952409597721717 18041169620995538399786411)
      ·
        refine ⟨27061754431493307599679617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18041169620995538399786411 27061754431493307599679617)
        ·
          refine ⟨20296315823619980699759713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27061754431493307599679617 20296315823619980699759713)
          ·
            refine ⟨15222236867714985524819785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20296315823619980699759713 15222236867714985524819785)
            ·
              refine ⟨11416677650786239143614839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15222236867714985524819785 11416677650786239143614839)
              ·
                refine ⟨17125016476179358715422259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11416677650786239143614839 17125016476179358715422259)
                ·
                  refine ⟨25687524714269038073133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17125016476179358715422259 25687524714269038073133389)
                  ·
                    refine ⟨9632821767850889277425021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25687524714269038073133389 9632821767850889277425021)
                    ·
                      refine ⟨3612308162944083479034383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632821767850889277425021 3612308162944083479034383)
                      ·
                        rfl

theorem cell23_7034945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7034945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034945 prefixEnd_7034945 := by exact prefixLift 7034945
  have htrace : WordTrace (prefixWord ++ tailWord_7034945) baseStart_7034945 baseEnd_7034945 := by
    simpa [prefixWord, tailWord_7034945, baseEnd_7034945] using wordTrace_append hprefix tailTrace_7034945
  have hstable : (prefixWord ++ tailWord_7034945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034945).length < 2 ^ (prefixWord ++ tailWord_7034945).sum := by decide
  have hdescent : baseEnd_7034945 < baseStart_7034945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034951 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_7034951 : Nat := 118140960795 + 7034951 * 2 ^ 59
def prefixEnd_7034951 : Nat := 4983230072969 + 3 ^ 40 * 7034951 * 2
def baseEnd_7034951 : Nat := 3612311243828010455559355

theorem tailTrace_7034951 : CollatzResearch.WordTrace tailWord_7034951 prefixEnd_7034951 3612311243828010455559355 := by
  unfold tailWord_7034951
  simp only [CollatzResearch.WordTrace]
  refine ⟨256585742336581475821680707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171057161557720983881120471 256585742336581475821680707)
  ·
    refine ⟨384878613504872213732521061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256585742336581475821680707 384878613504872213732521061)
    ·
      refine ⟨72164740032163540074847699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384878613504872213732521061 72164740032163540074847699)
      ·
        refine ⟨108247110048245310112271549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72164740032163540074847699 108247110048245310112271549)
        ·
          refine ⟨40592666268091991292101831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108247110048245310112271549 40592666268091991292101831)
          ·
            refine ⟨60888999402137986938152747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40592666268091991292101831 60888999402137986938152747)
            ·
              refine ⟨91333499103206980407229121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60888999402137986938152747 91333499103206980407229121)
              ·
                refine ⟨68500124327405235305421841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91333499103206980407229121 68500124327405235305421841)
                ·
                  refine ⟨51375093245553926479066381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68500124327405235305421841 51375093245553926479066381)
                  ·
                    refine ⟨19265659967082722429649893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51375093245553926479066381 19265659967082722429649893)
                    ·
                      refine ⟨3612311243828010455559355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19265659967082722429649893 3612311243828010455559355)
                      ·
                        rfl

theorem cell23_7034951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_7034951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034951 prefixEnd_7034951 := by exact prefixLift 7034951
  have htrace : WordTrace (prefixWord ++ tailWord_7034951) baseStart_7034951 baseEnd_7034951 := by
    simpa [prefixWord, tailWord_7034951, baseEnd_7034951] using wordTrace_append hprefix tailTrace_7034951
  have hstable : (prefixWord ++ tailWord_7034951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034951).length < 2 ^ (prefixWord ++ tailWord_7034951).sum := by decide
  have hdescent : baseEnd_7034951 < baseStart_7034951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034966 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7034966 : Nat := 118140960795 + 7034966 * 2 ^ 59
def prefixEnd_7034966 : Nat := 4983230072969 + 3 ^ 40 * 7034966 * 2
def baseEnd_7034966 : Nat := 3612318946037827896871787

theorem tailTrace_7034966 : CollatzResearch.WordTrace tailWord_7034966 prefixEnd_7034966 3612318946037827896871787 := by
  unfold tailWord_7034966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036643089470445836467297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171057526287684755588984501 16036643089470445836467297)
  ·
    refine ⟨12027482317102834377350473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16036643089470445836467297 12027482317102834377350473)
    ·
      refine ⟨9020611737827125783012855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12027482317102834377350473 9020611737827125783012855)
      ·
        refine ⟨13530917606740688674519283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020611737827125783012855 13530917606740688674519283)
        ·
          refine ⟨20296376410111033011778925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530917606740688674519283 20296376410111033011778925)
          ·
            refine ⟨7611141153791637379417097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20296376410111033011778925 7611141153791637379417097)
            ·
              refine ⟨5708355865343728034562823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611141153791637379417097 5708355865343728034562823)
              ·
                refine ⟨8562533798015592051844235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708355865343728034562823 8562533798015592051844235)
                ·
                  refine ⟨12843800697023388077766353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562533798015592051844235 12843800697023388077766353)
                  ·
                    refine ⟨9632850522767541058324765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12843800697023388077766353 9632850522767541058324765)
                    ·
                      refine ⟨3612318946037827896871787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9632850522767541058324765 3612318946037827896871787)
                      ·
                        rfl

theorem cell23_7034966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7034966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034966 prefixEnd_7034966 := by exact prefixLift 7034966
  have htrace : WordTrace (prefixWord ++ tailWord_7034966) baseStart_7034966 baseEnd_7034966 := by
    simpa [prefixWord, tailWord_7034966, baseEnd_7034966] using wordTrace_append hprefix tailTrace_7034966
  have hstable : (prefixWord ++ tailWord_7034966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034966).length < 2 ^ (prefixWord ++ tailWord_7034966).sum := by decide
  have hdescent : baseEnd_7034966 < baseStart_7034966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034972 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_7034972 : Nat := 118140960795 + 7034972 * 2 ^ 59
def prefixEnd_7034972 : Nat := 4983230072969 + 3 ^ 40 * 7034972 * 2
def baseEnd_7034972 : Nat := 3612322026921754873396759

theorem tailTrace_7034972 : CollatzResearch.WordTrace tailWord_7034972 prefixEnd_7034972 3612322026921754873396759 := by
  unfold tailWord_7034972
  simp only [CollatzResearch.WordTrace]
  refine ⟨128293254134752698204097585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171057672179670264272130113 128293254134752698204097585)
  ·
    refine ⟨96219940601064523653073189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128293254134752698204097585 96219940601064523653073189)
    ·
      refine ⟨18041238862699598184951223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96219940601064523653073189 18041238862699598184951223)
      ·
        refine ⟨27061858294049397277426835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18041238862699598184951223 27061858294049397277426835)
        ·
          refine ⟨40592787441074095916140253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27061858294049397277426835 40592787441074095916140253)
          ·
            refine ⟨15222295290402785968552595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40592787441074095916140253 15222295290402785968552595)
            ·
              refine ⟨22833442935604178952828893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222295290402785968552595 22833442935604178952828893)
              ·
                refine ⟨8562541100851567107310835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22833442935604178952828893 8562541100851567107310835)
                ·
                  refine ⟨12843811651277350660966253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562541100851567107310835 12843811651277350660966253)
                  ·
                    refine ⟨4816429369229006497862345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12843811651277350660966253 4816429369229006497862345)
                    ·
                      refine ⟨3612322026921754873396759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816429369229006497862345 3612322026921754873396759)
                      ·
                        rfl

theorem cell23_7034972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_7034972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034972 prefixEnd_7034972 := by exact prefixLift 7034972
  have htrace : WordTrace (prefixWord ++ tailWord_7034972) baseStart_7034972 baseEnd_7034972 := by
    simpa [prefixWord, tailWord_7034972, baseEnd_7034972] using wordTrace_append hprefix tailTrace_7034972
  have hstable : (prefixWord ++ tailWord_7034972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034972).length < 2 ^ (prefixWord ++ tailWord_7034972).sum := by decide
  have hdescent : baseEnd_7034972 < baseStart_7034972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034985 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 4, 2, 2]
def baseStart_7034985 : Nat := 118140960795 + 7034985 * 2 ^ 59
def prefixEnd_7034985 : Nat := 4983230072969 + 3 ^ 40 * 7034985 * 2
def baseEnd_7034985 : Nat := 3612328702170263322534199

theorem tailTrace_7034985 : CollatzResearch.WordTrace tailWord_7034985 prefixEnd_7034985 3612328702170263322534199 := by
  unfold tailWord_7034985
  simp only [CollatzResearch.WordTrace]
  refine ⟨256586982418458299628418409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171057988278972199752278939 256586982418458299628418409)
  ·
    refine ⟨192440236813843724721313807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256586982418458299628418409 192440236813843724721313807)
    ·
      refine ⟨288660355220765587081970711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192440236813843724721313807 288660355220765587081970711)
      ·
        refine ⟨432990532831148380622956067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288660355220765587081970711 432990532831148380622956067)
        ·
          refine ⟨649485799246722570934434101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432990532831148380622956067 649485799246722570934434101)
          ·
            refine ⟨60889293679380241025103197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 649485799246722570934434101 60889293679380241025103197)
            ·
              refine ⟨22833485129767590384413699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60889293679380241025103197 22833485129767590384413699)
              ·
                refine ⟨34250227694651385576620549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22833485129767590384413699 34250227694651385576620549)
                ·
                  refine ⟨6421917692747134795616353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34250227694651385576620549 6421917692747134795616353)
                  ·
                    refine ⟨4816438269560351096712265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6421917692747134795616353 4816438269560351096712265)
                    ·
                      refine ⟨3612328702170263322534199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816438269560351096712265 3612328702170263322534199)
                      ·
                        rfl

theorem cell23_7034985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2, 2].length) (baseStart_7034985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034985 prefixEnd_7034985 := by exact prefixLift 7034985
  have htrace : WordTrace (prefixWord ++ tailWord_7034985) baseStart_7034985 baseEnd_7034985 := by
    simpa [prefixWord, tailWord_7034985, baseEnd_7034985] using wordTrace_append hprefix tailTrace_7034985
  have hstable : (prefixWord ++ tailWord_7034985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034985).length < 2 ^ (prefixWord ++ tailWord_7034985).sum := by decide
  have hdescent : baseEnd_7034985 < baseStart_7034985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7034991 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 7]
def baseStart_7034991 : Nat := 118140960795 + 7034991 * 2 ^ 59
def prefixEnd_7034991 : Nat := 4983230072969 + 3 ^ 40 * 7034991 * 2
def baseEnd_7034991 : Nat := 401370198117132255451019

theorem tailTrace_7034991 : CollatzResearch.WordTrace tailWord_7034991 prefixEnd_7034991 401370198117132255451019 := by
  unfold tailWord_7034991
  simp only [CollatzResearch.WordTrace]
  refine ⟨256587201256436562653136827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171058134170957708435424551 256587201256436562653136827)
  ·
    refine ⟨384880801884654843979705241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256587201256436562653136827 384880801884654843979705241)
    ·
      refine ⟨288660601413491132984778931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384880801884654843979705241 288660601413491132984778931)
      ·
        refine ⟨432990902120236699477168397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288660601413491132984778931 432990902120236699477168397)
        ·
          refine ⟨162371588295088762303938149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432990902120236699477168397 162371588295088762303938149)
          ·
            refine ⟨30444672805329142931988403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162371588295088762303938149 30444672805329142931988403)
            ·
              refine ⟨45667009207993714397982605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30444672805329142931988403 45667009207993714397982605)
              ·
                refine ⟨17125128452997642899243477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45667009207993714397982605 17125128452997642899243477)
                ·
                  refine ⟨401370198117132255451019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17125128452997642899243477 401370198117132255451019)
                  ·
                    rfl

theorem cell23_7034991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 7].length) (baseStart_7034991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7034991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7034991 prefixEnd_7034991 := by exact prefixLift 7034991
  have htrace : WordTrace (prefixWord ++ tailWord_7034991) baseStart_7034991 baseEnd_7034991 := by
    simpa [prefixWord, tailWord_7034991, baseEnd_7034991] using wordTrace_append hprefix tailTrace_7034991
  have hstable : (prefixWord ++ tailWord_7034991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7034991).length < 2 ^ (prefixWord ++ tailWord_7034991).sum := by decide
  have hdescent : baseEnd_7034991 < baseStart_7034991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7034991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035058 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7035058 : Nat := 118140960795 + 7035058 * 2 ^ 59
def prefixEnd_7035058 : Nat := 4983230072969 + 3 ^ 40 * 7035058 * 2
def baseEnd_7035058 : Nat := 3612366186258041536921363

theorem tailTrace_7035058 : CollatzResearch.WordTrace tailWord_7035058 prefixEnd_7035058 3612366186258041536921363 := by
  unfold tailWord_7035058
  simp only [CollatzResearch.WordTrace]
  refine ⟨64147411236798458273956457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171059763298129222063883885 64147411236798458273956457)
  ·
    refine ⟨48110558427598843705467343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64147411236798458273956457 48110558427598843705467343)
    ·
      refine ⟨72165837641398265558201015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48110558427598843705467343 72165837641398265558201015)
      ·
        refine ⟨108248756462097398337301523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72165837641398265558201015 108248756462097398337301523)
        ·
          refine ⟨162373134693146097505952285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108248756462097398337301523 162373134693146097505952285)
          ·
            refine ⟨60889925509929786564732107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162373134693146097505952285 60889925509929786564732107)
            ·
              refine ⟨91334888264894679847098161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60889925509929786564732107 91334888264894679847098161)
              ·
                refine ⟨68501166198671009885323621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91334888264894679847098161 68501166198671009885323621)
                ·
                  refine ⟨12843968662250814353498179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68501166198671009885323621 12843968662250814353498179)
                  ·
                    refine ⟨19265952993376221530247269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12843968662250814353498179 19265952993376221530247269)
                    ·
                      refine ⟨3612366186258041536921363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19265952993376221530247269 3612366186258041536921363)
                      ·
                        rfl

theorem cell23_7035058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7035058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035058 prefixEnd_7035058 := by exact prefixLift 7035058
  have htrace : WordTrace (prefixWord ++ tailWord_7035058) baseStart_7035058 baseEnd_7035058 := by
    simpa [prefixWord, tailWord_7035058, baseEnd_7035058] using wordTrace_append hprefix tailTrace_7035058
  have hstable : (prefixWord ++ tailWord_7035058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035058).length < 2 ^ (prefixWord ++ tailWord_7035058).sum := by decide
  have hdescent : baseEnd_7035058 < baseStart_7035058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035071 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_7035071 : Nat := 118140960795 + 7035071 * 2 ^ 59
def prefixEnd_7035071 : Nat := 4983230072969 + 3 ^ 40 * 7035071 * 2
def baseEnd_7035071 : Nat := 3612372861506549986058803

theorem tailTrace_7035071 : CollatzResearch.WordTrace tailWord_7035071 prefixEnd_7035071 3612372861506549986058803 := by
  unfold tailWord_7035071
  simp only [CollatzResearch.WordTrace]
  refine ⟨256590119096146736316049067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171060079397431157544032711 256590119096146736316049067)
  ·
    refine ⟨384885178644220104474073601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256590119096146736316049067 384885178644220104474073601)
    ·
      refine ⟨288663883983165078355555201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384885178644220104474073601 288663883983165078355555201)
      ·
        refine ⟨216497912987373808766666401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288663883983165078355555201 216497912987373808766666401)
        ·
          refine ⟨162373434740530356574999801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216497912987373808766666401 162373434740530356574999801)
          ·
            refine ⟨121780076055397767431249851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162373434740530356574999801 121780076055397767431249851)
            ·
              refine ⟨182670114083096651146874777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121780076055397767431249851 182670114083096651146874777)
              ·
                refine ⟨137002585562322488360156083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182670114083096651146874777 137002585562322488360156083)
                ·
                  refine ⟨205503878343483732540234125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137002585562322488360156083 205503878343483732540234125)
                  ·
                    refine ⟨77063954378806399702587797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205503878343483732540234125 77063954378806399702587797)
                    ·
                      refine ⟨3612372861506549986058803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77063954378806399702587797 3612372861506549986058803)
                      ·
                        rfl

theorem cell23_7035071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_7035071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035071 prefixEnd_7035071 := by exact prefixLift 7035071
  have htrace : WordTrace (prefixWord ++ tailWord_7035071) baseStart_7035071 baseEnd_7035071 := by
    simpa [prefixWord, tailWord_7035071, baseEnd_7035071] using wordTrace_append hprefix tailTrace_7035071
  have hstable : (prefixWord ++ tailWord_7035071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035071).length < 2 ^ (prefixWord ++ tailWord_7035071).sum := by decide
  have hdescent : baseEnd_7035071 < baseStart_7035071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035081 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 8]
def baseStart_7035081 : Nat := 118140960795 + 7035081 * 2 ^ 59
def prefixEnd_7035081 : Nat := 4983230072969 + 3 ^ 40 * 7035081 * 2
def baseEnd_7035081 : Nat := 401375332923677216325973

theorem tailTrace_7035081 : CollatzResearch.WordTrace tailWord_7035081 prefixEnd_7035081 401375332923677216325973 := by
  unfold tailWord_7035081
  simp only [CollatzResearch.WordTrace]
  refine ⟨256590483826110508023913097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171060322550740338682608731 256590483826110508023913097)
  ·
    refine ⟨192442862869582881017934823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256590483826110508023913097 192442862869582881017934823)
    ·
      refine ⟨288664294304374321526902235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192442862869582881017934823 288664294304374321526902235)
      ·
        refine ⟨432996441456561482290353353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288664294304374321526902235 432996441456561482290353353)
        ·
          refine ⟨324747331092421111717765015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432996441456561482290353353 324747331092421111717765015)
          ·
            refine ⟨487120996638631667576647523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324747331092421111717765015 487120996638631667576647523)
            ·
              refine ⟨730681494957947501364971285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487120996638631667576647523 730681494957947501364971285)
              ·
                refine ⟨34250695076153789126483029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 730681494957947501364971285 34250695076153789126483029)
                ·
                  refine ⟨401375332923677216325973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34250695076153789126483029 401375332923677216325973)
                  ·
                    rfl

theorem cell23_7035081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_7035081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035081 prefixEnd_7035081 := by exact prefixLift 7035081
  have htrace : WordTrace (prefixWord ++ tailWord_7035081) baseStart_7035081 baseEnd_7035081 := by
    simpa [prefixWord, tailWord_7035081, baseEnd_7035081] using wordTrace_append hprefix tailTrace_7035081
  have hstable : (prefixWord ++ tailWord_7035081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035081).length < 2 ^ (prefixWord ++ tailWord_7035081).sum := by decide
  have hdescent : baseEnd_7035081 < baseStart_7035081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035098 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_7035098 : Nat := 118140960795 + 7035098 * 2 ^ 59
def prefixEnd_7035098 : Nat := 4983230072969 + 3 ^ 40 * 7035098 * 2
def baseEnd_7035098 : Nat := 401376302831580153380131

theorem tailTrace_7035098 : CollatzResearch.WordTrace tailWord_7035098 prefixEnd_7035098 401376302831580153380131 := by
  unfold tailWord_7035098
  simp only [CollatzResearch.WordTrace]
  refine ⟨64147775966762229981820487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171060735911365946618187965 64147775966762229981820487)
  ·
    refine ⟨96221663950143344972730731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64147775966762229981820487 96221663950143344972730731)
    ·
      refine ⟨144332495925215017459096097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96221663950143344972730731 144332495925215017459096097)
      ·
        refine ⟨108249371943911263094322073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144332495925215017459096097 108249371943911263094322073)
        ·
          refine ⟨81187028957933447320741555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108249371943911263094322073 81187028957933447320741555)
          ·
            refine ⟨121780543436900170981112333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81187028957933447320741555 121780543436900170981112333)
            ·
              refine ⟨45667703788837564117917125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121780543436900170981112333 45667703788837564117917125)
              ·
                refine ⟨8562694460407043272109461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45667703788837564117917125 8562694460407043272109461)
                ·
                  refine ⟨401376302831580153380131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8562694460407043272109461 401376302831580153380131)
                  ·
                    rfl

theorem cell23_7035098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_7035098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035098 prefixEnd_7035098 := by exact prefixLift 7035098
  have htrace : WordTrace (prefixWord ++ tailWord_7035098) baseStart_7035098 baseEnd_7035098 := by
    simpa [prefixWord, tailWord_7035098, baseEnd_7035098] using wordTrace_append hprefix tailTrace_7035098
  have hstable : (prefixWord ++ tailWord_7035098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035098).length < 2 ^ (prefixWord ++ tailWord_7035098).sum := by decide
  have hdescent : baseEnd_7035098 < baseStart_7035098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035108 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_7035108 : Nat := 118140960795 + 7035108 * 2 ^ 59
def prefixEnd_7035108 : Nat := 4983230072969 + 3 ^ 40 * 7035108 * 2
def baseEnd_7035108 : Nat := 3612391860290766341296133

theorem tailTrace_7035108 : CollatzResearch.WordTrace tailWord_7035108 prefixEnd_7035108 3612391860290766341296133 := by
  unfold tailWord_7035108
  simp only [CollatzResearch.WordTrace]
  refine ⟨128295734298506345817572989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171060979064675127756763985 128295734298506345817572989)
  ·
    refine ⟨48110900361939879681589871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128295734298506345817572989 48110900361939879681589871)
    ·
      refine ⟨72166350542909819522384807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48110900361939879681589871 72166350542909819522384807)
      ·
        refine ⟨108249525814364729283577211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72166350542909819522384807 108249525814364729283577211)
        ·
          refine ⟨162374288721547093925365817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108249525814364729283577211 162374288721547093925365817)
          ·
            refine ⟨121780716541160320444024363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162374288721547093925365817 121780716541160320444024363)
            ·
              refine ⟨182671074811740480666036545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121780716541160320444024363 182671074811740480666036545)
              ·
                refine ⟨137003306108805360499527409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182671074811740480666036545 137003306108805360499527409)
                ·
                  refine ⟨102752479581604020374645557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137003306108805360499527409 102752479581604020374645557)
                  ·
                    refine ⟨9633044960775376910123021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102752479581604020374645557 9633044960775376910123021)
                    ·
                      refine ⟨3612391860290766341296133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9633044960775376910123021 3612391860290766341296133)
                      ·
                        rfl

theorem cell23_7035108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_7035108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035108 prefixEnd_7035108 := by exact prefixLift 7035108
  have htrace : WordTrace (prefixWord ++ tailWord_7035108) baseStart_7035108 baseEnd_7035108 := by
    simpa [prefixWord, tailWord_7035108, baseEnd_7035108] using wordTrace_append hprefix tailTrace_7035108
  have hstable : (prefixWord ++ tailWord_7035108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035108).length < 2 ^ (prefixWord ++ tailWord_7035108).sum := by decide
  have hdescent : baseEnd_7035108 < baseStart_7035108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035135 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 5, 2]
def baseStart_7035135 : Nat := 118140960795 + 7035135 * 2 ^ 59
def prefixEnd_7035135 : Nat := 4983230072969 + 3 ^ 40 * 7035135 * 2
def baseEnd_7035135 : Nat := 3612405724268437735658509

theorem tailTrace_7035135 : CollatzResearch.WordTrace tailWord_7035135 prefixEnd_7035135 3612405724268437735658509 := by
  unfold tailWord_7035135
  simp only [CollatzResearch.WordTrace]
  refine ⟨256592453367914875246378859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171061635578609916830919239 256592453367914875246378859)
  ·
    refine ⟨384888680051872312869568289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256592453367914875246378859 384888680051872312869568289)
    ·
      refine ⟨288666510038904234652176217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384888680051872312869568289 288666510038904234652176217)
      ·
        refine ⟨216499882529178175989132163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288666510038904234652176217 216499882529178175989132163)
        ·
          refine ⟨324749823793767263983698245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216499882529178175989132163 324749823793767263983698245)
          ·
            refine ⟨60890591961331361996943421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324749823793767263983698245 60890591961331361996943421)
            ·
              refine ⟨22833971985499260748853783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60890591961331361996943421 22833971985499260748853783)
              ·
                refine ⟨34250957978248891123280675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22833971985499260748853783 34250957978248891123280675)
                ·
                  refine ⟨51376436967373336684921013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34250957978248891123280675 51376436967373336684921013)
                  ·
                    refine ⟨4816540965691250314211345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51376436967373336684921013 4816540965691250314211345)
                    ·
                      refine ⟨3612405724268437735658509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816540965691250314211345 3612405724268437735658509)
                      ·
                        rfl

theorem cell23_7035135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_7035135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035135 prefixEnd_7035135 := by exact prefixLift 7035135
  have htrace : WordTrace (prefixWord ++ tailWord_7035135) baseStart_7035135 baseEnd_7035135 := by
    simpa [prefixWord, tailWord_7035135, baseEnd_7035135] using wordTrace_append hprefix tailTrace_7035135
  have hstable : (prefixWord ++ tailWord_7035135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035135).length < 2 ^ (prefixWord ++ tailWord_7035135).sum := by decide
  have hdescent : baseEnd_7035135 < baseStart_7035135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035145 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_7035145 : Nat := 118140960795 + 7035145 * 2 ^ 59
def prefixEnd_7035145 : Nat := 4983230072969 + 3 ^ 40 * 7035145 * 2
def baseEnd_7035145 : Nat := 1204136953024994232177821

theorem tailTrace_7035145 : CollatzResearch.WordTrace tailWord_7035145 prefixEnd_7035145 1204136953024994232177821 := by
  unfold tailWord_7035145
  simp only [CollatzResearch.WordTrace]
  refine ⟨256592818097878646954242889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171061878731919097969495259 256592818097878646954242889)
  ·
    refine ⟨192444613573408985215682167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256592818097878646954242889 192444613573408985215682167)
    ·
      refine ⟨288666920360113477823523251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192444613573408985215682167 288666920360113477823523251)
      ·
        refine ⟨433000380540170216735284877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288666920360113477823523251 433000380540170216735284877)
        ·
          refine ⟨162375142702563831275731829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433000380540170216735284877 162375142702563831275731829)
          ·
            refine ⟨15222669628365359182099859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162375142702563831275731829 15222669628365359182099859)
            ·
              refine ⟨22834004442548038773149789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222669628365359182099859 22834004442548038773149789)
              ·
                refine ⟨8562751665955514539931171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22834004442548038773149789 8562751665955514539931171)
                ·
                  refine ⟨12844127498933271809896757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562751665955514539931171 12844127498933271809896757)
                  ·
                    refine ⟨1204136953024994232177821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12844127498933271809896757 1204136953024994232177821)
                    ·
                      rfl

theorem cell23_7035145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_7035145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035145 prefixEnd_7035145 := by exact prefixLift 7035145
  have htrace : WordTrace (prefixWord ++ tailWord_7035145) baseStart_7035145 baseEnd_7035145 := by
    simpa [prefixWord, tailWord_7035145, baseEnd_7035145] using wordTrace_append hprefix tailTrace_7035145
  have hstable : (prefixWord ++ tailWord_7035145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035145).length < 2 ^ (prefixWord ++ tailWord_7035145).sum := by decide
  have hdescent : baseEnd_7035145 < baseStart_7035145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035159 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7035159 : Nat := 118140960795 + 7035159 * 2 ^ 59
def prefixEnd_7035159 : Nat := 4983230072969 + 3 ^ 40 * 7035159 * 2
def baseEnd_7035159 : Nat := 3612418047804145641758399

theorem tailTrace_7035159 : CollatzResearch.WordTrace tailWord_7035159 prefixEnd_7035159 3612418047804145641758399 := by
  unfold tailWord_7035159
  simp only [CollatzResearch.WordTrace]
  refine ⟨256593328719827927345252531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171062219146551951563501687 256593328719827927345252531)
  ·
    refine ⟨384889993079741891017878797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256593328719827927345252531 384889993079741891017878797)
    ·
      refine ⟨144333747404903209131704549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384889993079741891017878797 144333747404903209131704549)
      ·
        refine ⟨27062577638419351712194603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144333747404903209131704549 27062577638419351712194603)
        ·
          refine ⟨40593866457629027568291905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27062577638419351712194603 40593866457629027568291905)
          ·
            refine ⟨30445399843221770676218929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40593866457629027568291905 30445399843221770676218929)
            ·
              refine ⟨22834049882416328007164197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30445399843221770676218929 22834049882416328007164197)
              ·
                refine ⟨4281384352953061501343287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22834049882416328007164197 4281384352953061501343287)
                ·
                  refine ⟨6422076529429592252014931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281384352953061501343287 6422076529429592252014931)
                  ·
                    refine ⟨9633114794144388378022397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422076529429592252014931 9633114794144388378022397)
                    ·
                      refine ⟨3612418047804145641758399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9633114794144388378022397 3612418047804145641758399)
                      ·
                        rfl

theorem cell23_7035159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7035159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035159 prefixEnd_7035159 := by exact prefixLift 7035159
  have htrace : WordTrace (prefixWord ++ tailWord_7035159) baseStart_7035159 baseEnd_7035159 := by
    simpa [prefixWord, tailWord_7035159, baseEnd_7035159] using wordTrace_append hprefix tailTrace_7035159
  have hstable : (prefixWord ++ tailWord_7035159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035159).length < 2 ^ (prefixWord ++ tailWord_7035159).sum := by decide
  have hdescent : baseEnd_7035159 < baseStart_7035159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035225 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 7, 2]
def baseStart_7035225 : Nat := 118140960795 + 7035225 * 2 ^ 59
def prefixEnd_7035225 : Nat := 4983230072969 + 3 ^ 40 * 7035225 * 2
def baseEnd_7035225 : Nat := 3612451937527342383533095

theorem tailTrace_7035225 : CollatzResearch.WordTrace tailWord_7035225 prefixEnd_7035225 3612451937527342383533095 := by
  unfold tailWord_7035225
  simp only [CollatzResearch.WordTrace]
  refine ⟨256595735937588820617155129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171063823958392547078103419 256595735937588820617155129)
  ·
    refine ⟨192446801953191615462866347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256595735937588820617155129 192446801953191615462866347)
    ·
      refine ⟨288670202929787423194299521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192446801953191615462866347 288670202929787423194299521)
      ·
        refine ⟨216502652197340567395724641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288670202929787423194299521 216502652197340567395724641)
        ·
          refine ⟨162376989148005425546793481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216502652197340567395724641 162376989148005425546793481)
          ·
            refine ⟨121782741861004069160095111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162376989148005425546793481 121782741861004069160095111)
            ·
              refine ⟨182674112791506103740142667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121782741861004069160095111 182674112791506103740142667)
              ·
                refine ⟨274011169187259155610214001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182674112791506103740142667 274011169187259155610214001)
                ·
                  refine ⟨205508376890444366707660501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274011169187259155610214001 205508376890444366707660501)
                  ·
                    refine ⟨4816602583369789844710793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 205508376890444366707660501 4816602583369789844710793)
                    ·
                      refine ⟨3612451937527342383533095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816602583369789844710793 3612451937527342383533095)
                      ·
                        rfl

theorem cell23_7035225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_7035225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035225 prefixEnd_7035225 := by exact prefixLift 7035225
  have htrace : WordTrace (prefixWord ++ tailWord_7035225) baseStart_7035225 baseEnd_7035225 := by
    simpa [prefixWord, tailWord_7035225, baseEnd_7035225] using wordTrace_append hprefix tailTrace_7035225
  have hstable : (prefixWord ++ tailWord_7035225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035225).length < 2 ^ (prefixWord ++ tailWord_7035225).sum := by decide
  have hdescent : baseEnd_7035225 < baseStart_7035225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035230 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7035230 : Nat := 118140960795 + 7035230 * 2 ^ 59
def prefixEnd_7035230 : Nat := 4983230072969 + 3 ^ 40 * 7035230 * 2
def baseEnd_7035230 : Nat := 1204151501643538287990191

theorem tailTrace_7035230 : CollatzResearch.WordTrace tailWord_7035230 prefixEnd_7035230 1204151501643538287990191 := by
  unfold tailWord_7035230
  simp only [CollatzResearch.WordTrace]
  refine ⟨32074489787821338308885893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171063945535047137647391429 32074489787821338308885893)
  ·
    refine ⟨6013966835216500932916105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32074489787821338308885893 6013966835216500932916105)
    ·
      refine ⟨4510475126412375699687079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6013966835216500932916105 4510475126412375699687079)
      ·
        refine ⟨6765712689618563549530619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4510475126412375699687079 6765712689618563549530619)
        ·
          refine ⟨10148569034427845324295929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765712689618563549530619 10148569034427845324295929)
          ·
            refine ⟨7611426775820883993221947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148569034427845324295929 7611426775820883993221947)
            ·
              refine ⟨11417140163731325989832921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7611426775820883993221947 11417140163731325989832921)
              ·
                refine ⟨8562855122798494492374691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11417140163731325989832921 8562855122798494492374691)
                ·
                  refine ⟨12844282684197741738562037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562855122798494492374691 12844282684197741738562037)
                  ·
                    refine ⟨1204151501643538287990191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12844282684197741738562037 1204151501643538287990191)
                    ·
                      rfl

theorem cell23_7035230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7035230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035230 prefixEnd_7035230 := by exact prefixLift 7035230
  have htrace : WordTrace (prefixWord ++ tailWord_7035230) baseStart_7035230 baseEnd_7035230 := by
    simpa [prefixWord, tailWord_7035230, baseEnd_7035230] using wordTrace_append hprefix tailTrace_7035230
  have hstable : (prefixWord ++ tailWord_7035230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035230).length < 2 ^ (prefixWord ++ tailWord_7035230).sum := by decide
  have hdescent : baseEnd_7035230 < baseStart_7035230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035272 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_7035272 : Nat := 118140960795 + 7035272 * 2 ^ 59
def prefixEnd_7035272 : Nat := 4983230072969 + 3 ^ 40 * 7035272 * 2
def baseEnd_7035272 : Nat := 3612476071118103699645379

theorem tailTrace_7035272 : CollatzResearch.WordTrace tailWord_7035272 prefixEnd_7035272 3612476071118103699645379 := by
  unfold tailWord_7035272
  simp only [CollatzResearch.WordTrace]
  refine ⟨128298725084209273822058035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171064966778945698429410713 128298725084209273822058035)
  ·
    refine ⟨192448087626313910733087053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128298725084209273822058035 192448087626313910733087053)
    ·
      refine ⟨72168032859867716524907645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192448087626313910733087053 72168032859867716524907645)
      ·
        refine ⟨27063012322450393696840367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72168032859867716524907645 27063012322450393696840367)
        ·
          refine ⟨40594518483675590545260551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27063012322450393696840367 40594518483675590545260551)
          ·
            refine ⟨60891777725513385817890827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40594518483675590545260551 60891777725513385817890827)
            ·
              refine ⟨91337666588270078726836241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60891777725513385817890827 91337666588270078726836241)
              ·
                refine ⟨68503249941202559045127181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91337666588270078726836241 68503249941202559045127181)
                ·
                  refine ⟨25688718727950959641922693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68503249941202559045127181 25688718727950959641922693)
                  ·
                    refine ⟨4816634761490804932860505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25688718727950959641922693 4816634761490804932860505)
                    ·
                      refine ⟨3612476071118103699645379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816634761490804932860505 3612476071118103699645379)
                      ·
                        rfl

theorem cell23_7035272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_7035272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035272 prefixEnd_7035272 := by exact prefixLift 7035272
  have htrace : WordTrace (prefixWord ++ tailWord_7035272) baseStart_7035272 baseEnd_7035272 := by
    simpa [prefixWord, tailWord_7035272, baseEnd_7035272] using wordTrace_append hprefix tailTrace_7035272
  have hstable : (prefixWord ++ tailWord_7035272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035272).length < 2 ^ (prefixWord ++ tailWord_7035272).sum := by decide
  have hdescent : baseEnd_7035272 < baseStart_7035272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035275 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3]
def baseStart_7035275 : Nat := 118140960795 + 7035275 * 2 ^ 59
def prefixEnd_7035275 : Nat := 4983230072969 + 3 ^ 40 * 7035275 * 2
def baseEnd_7035275 : Nat := 3612477611560067187907865

theorem tailTrace_7035275 : CollatzResearch.WordTrace tailWord_7035275 prefixEnd_7035275 3612477611560067187907865 := by
  unfold tailWord_7035275
  simp only [CollatzResearch.WordTrace]
  refine ⟨256597559587407679156475279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171065039724938452770983519 256597559587407679156475279)
  ·
    refine ⟨384896339381111518734712919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256597559587407679156475279 384896339381111518734712919)
    ·
      refine ⟨577344509071667278102069379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384896339381111518734712919 577344509071667278102069379)
      ·
        refine ⟨866016763607500917153104069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577344509071667278102069379 866016763607500917153104069)
        ·
          refine ⟨162378143176406421966207013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 866016763607500917153104069 162378143176406421966207013)
          ·
            refine ⟨30445901845576204118663815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162378143176406421966207013 30445901845576204118663815)
            ·
              refine ⟨45668852768364306177995723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30445901845576204118663815 45668852768364306177995723)
              ·
                refine ⟨68503279152546459266993585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45668852768364306177995723 68503279152546459266993585)
                ·
                  refine ⟨51377459364409844450245189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68503279152546459266993585 51377459364409844450245189)
                  ·
                    refine ⟨9633273630826845834420973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51377459364409844450245189 9633273630826845834420973)
                    ·
                      refine ⟨3612477611560067187907865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9633273630826845834420973 3612477611560067187907865)
                      ·
                        rfl

theorem cell23_7035275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3].length) (baseStart_7035275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035275 prefixEnd_7035275 := by exact prefixLift 7035275
  have htrace : WordTrace (prefixWord ++ tailWord_7035275) baseStart_7035275 baseEnd_7035275 := by
    simpa [prefixWord, tailWord_7035275, baseEnd_7035275] using wordTrace_append hprefix tailTrace_7035275
  have hstable : (prefixWord ++ tailWord_7035275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035275).length < 2 ^ (prefixWord ++ tailWord_7035275).sum := by decide
  have hdescent : baseEnd_7035275 < baseStart_7035275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035289 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 2, 2, 2]
def baseStart_7035289 : Nat := 118140960795 + 7035289 * 2 ^ 59
def prefixEnd_7035289 : Nat := 4983230072969 + 3 ^ 40 * 7035289 * 2
def baseEnd_7035289 : Nat := 3612484800289230133132801

theorem tailTrace_7035289 : CollatzResearch.WordTrace tailWord_7035289 prefixEnd_7035289 3612484800289230133132801 := by
  unfold tailWord_7035289
  simp only [CollatzResearch.WordTrace]
  refine ⟨256598070209356959547484921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171065380139571306364989947 256598070209356959547484921)
  ·
    refine ⟨192448552657017719660613691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256598070209356959547484921 192448552657017719660613691)
    ·
      refine ⟨288672828985526579490920537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192448552657017719660613691 288672828985526579490920537)
      ·
        refine ⟨216504621739144934618190403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288672828985526579490920537 216504621739144934618190403)
        ·
          refine ⟨324756932608717401927285605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216504621739144934618190403 324756932608717401927285605)
          ·
            refine ⟨60891924864134512861366051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324756932608717401927285605 60891924864134512861366051)
            ·
              refine ⟨91337887296201769292049077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60891924864134512861366051 91337887296201769292049077)
              ·
                refine ⟨8562926934018915871129601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91337887296201769292049077 8562926934018915871129601)
                ·
                  refine ⟨6422195200514186903347201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8562926934018915871129601 6422195200514186903347201)
                  ·
                    refine ⟨4816646400385640177510401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6422195200514186903347201 4816646400385640177510401)
                    ·
                      refine ⟨3612484800289230133132801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816646400385640177510401 3612484800289230133132801)
                      ·
                        rfl

theorem cell23_7035289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_7035289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035289 prefixEnd_7035289 := by exact prefixLift 7035289
  have htrace : WordTrace (prefixWord ++ tailWord_7035289) baseStart_7035289 baseEnd_7035289 := by
    simpa [prefixWord, tailWord_7035289, baseEnd_7035289] using wordTrace_append hprefix tailTrace_7035289
  have hstable : (prefixWord ++ tailWord_7035289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035289).length < 2 ^ (prefixWord ++ tailWord_7035289).sum := by decide
  have hdescent : baseEnd_7035289 < baseStart_7035289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035295 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 7]
def baseStart_7035295 : Nat := 118140960795 + 7035295 * 2 ^ 59
def prefixEnd_7035295 : Nat := 4983230072969 + 3 ^ 40 * 7035295 * 2
def baseEnd_7035295 : Nat := 401387542352573012184197

theorem tailTrace_7035295 : CollatzResearch.WordTrace tailWord_7035295 prefixEnd_7035295 401387542352573012184197 := by
  unfold tailWord_7035295
  simp only [CollatzResearch.WordTrace]
  refine ⟨256598289047335222572203339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171065526031556815048135559 256598289047335222572203339)
  ·
    refine ⟨384897433571002833858305009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256598289047335222572203339 384897433571002833858305009)
    ·
      refine ⟨288673075178252125393728757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384897433571002833858305009 288673075178252125393728757)
      ·
        refine ⟨27063100797961136755662071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288673075178252125393728757 27063100797961136755662071)
        ·
          refine ⟨40594651196941705133493107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27063100797961136755662071 40594651196941705133493107)
          ·
            refine ⟨60891976795412557700239661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40594651196941705133493107 60891976795412557700239661)
            ·
              refine ⟨22834491298279709137589873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60891976795412557700239661 22834491298279709137589873)
              ·
                refine ⟨17125868473709781853192405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22834491298279709137589873 17125868473709781853192405)
                ·
                  refine ⟨401387542352573012184197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17125868473709781853192405 401387542352573012184197)
                  ·
                    rfl

theorem cell23_7035295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 7].length) (baseStart_7035295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035295 prefixEnd_7035295 := by exact prefixLift 7035295
  have htrace : WordTrace (prefixWord ++ tailWord_7035295) baseStart_7035295 baseEnd_7035295 := by
    simpa [prefixWord, tailWord_7035295, baseEnd_7035295] using wordTrace_append hprefix tailTrace_7035295
  have hstable : (prefixWord ++ tailWord_7035295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035295).length < 2 ^ (prefixWord ++ tailWord_7035295).sum := by decide
  have hdescent : baseEnd_7035295 < baseStart_7035295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035385 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 8]
def baseStart_7035385 : Nat := 118140960795 + 7035385 * 2 ^ 59
def prefixEnd_7035385 : Nat := 4983230072969 + 3 ^ 40 * 7035385 * 2
def baseEnd_7035385 : Nat := 401392677159117973059151

theorem tailTrace_7035385 : CollatzResearch.WordTrace tailWord_7035385 prefixEnd_7035385 401392677159117973059151 := by
  unfold tailWord_7035385
  simp only [CollatzResearch.WordTrace]
  refine ⟨256601571617009167942979609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171067714411339445295319739 256601571617009167942979609)
  ·
    refine ⟨192451178712756875957234707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256601571617009167942979609 192451178712756875957234707)
    ·
      refine ⟨288676768069135313935852061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192451178712756875957234707 288676768069135313935852061)
      ·
        refine ⟨108253788025925742725944523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288676768069135313935852061 108253788025925742725944523)
        ·
          refine ⟨162380682038888614088916785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108253788025925742725944523 162380682038888614088916785)
          ·
            refine ⟨121785511529166460566687589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162380682038888614088916785 121785511529166460566687589)
            ·
              refine ⟨22834783411718711356253923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121785511529166460566687589 22834783411718711356253923)
              ·
                refine ⟨34252175117578067034380885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22834783411718711356253923 34252175117578067034380885)
                ·
                  refine ⟨401392677159117973059151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34252175117578067034380885 401392677159117973059151)
                  ·
                    rfl

theorem cell23_7035385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_7035385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035385 prefixEnd_7035385 := by exact prefixLift 7035385
  have htrace : WordTrace (prefixWord ++ tailWord_7035385) baseStart_7035385 baseEnd_7035385 := by
    simpa [prefixWord, tailWord_7035385, baseEnd_7035385] using wordTrace_append hprefix tailTrace_7035385
  have hstable : (prefixWord ++ tailWord_7035385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035385).length < 2 ^ (prefixWord ++ tailWord_7035385).sum := by decide
  have hdescent : baseEnd_7035385 < baseStart_7035385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035402 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_7035402 : Nat := 118140960795 + 7035402 * 2 ^ 59
def prefixEnd_7035402 : Nat := 4983230072969 + 3 ^ 40 * 7035402 * 2
def baseEnd_7035402 : Nat := 401393647067020910113309

theorem tailTrace_7035402 : CollatzResearch.WordTrace tailWord_7035402 prefixEnd_7035402 401393647067020910113309 := by
  unfold tailWord_7035402
  simp only [CollatzResearch.WordTrace]
  refine ⟨64150547914486894961587115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171068127771965053230898973 64150547914486894961587115)
  ·
    refine ⟨96225821871730342442380673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64150547914486894961587115 96225821871730342442380673)
    ·
      refine ⟨72169366403797756831785505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96225821871730342442380673 72169366403797756831785505)
      ·
        refine ⟨54127024802848317623839129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72169366403797756831785505 54127024802848317623839129)
        ·
          refine ⟨40595268602136238217879347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54127024802848317623839129 40595268602136238217879347)
          ·
            refine ⟨60892902903204357326819021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40595268602136238217879347 60892902903204357326819021)
            ·
              refine ⟨22834838588701633997557133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60892902903204357326819021 22834838588701633997557133)
              ·
                refine ⟨8563064470763112749083925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22834838588701633997557133 8563064470763112749083925)
                ·
                  refine ⟨401393647067020910113309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8563064470763112749083925 401393647067020910113309)
                  ·
                    rfl

theorem cell23_7035402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_7035402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035402 prefixEnd_7035402 := by exact prefixLift 7035402
  have htrace : WordTrace (prefixWord ++ tailWord_7035402) baseStart_7035402 baseEnd_7035402 := by
    simpa [prefixWord, tailWord_7035402, baseEnd_7035402] using wordTrace_append hprefix tailTrace_7035402
  have hstable : (prefixWord ++ tailWord_7035402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035402).length < 2 ^ (prefixWord ++ tailWord_7035402).sum := by decide
  have hdescent : baseEnd_7035402 < baseStart_7035402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035496 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_7035496 : Nat := 118140960795 + 7035496 * 2 ^ 59
def prefixEnd_7035496 : Nat := 4983230072969 + 3 ^ 40 * 7035496 * 2
def baseEnd_7035496 : Nat := 1204197030261570274414783

theorem tailTrace_7035496 : CollatzResearch.WordTrace tailWord_7035496 prefixEnd_7035496 1204197030261570274414783 := by
  unfold tailWord_7035496
  simp only [CollatzResearch.WordTrace]
  refine ⟨128302810059803516950135171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171070413413071355933513561 128302810059803516950135171)
  ·
    refine ⟨192454215089705275425202757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128302810059803516950135171 192454215089705275425202757)
    ·
      refine ⟨36085165329319739142225517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192454215089705275425202757 36085165329319739142225517)
      ·
        refine ⟨13531936998494902178334569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36085165329319739142225517 13531936998494902178334569)
        ·
          refine ⟨10148952748871176633750927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13531936998494902178334569 10148952748871176633750927)
          ·
            refine ⟨15223429123306764950626391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10148952748871176633750927 15223429123306764950626391)
            ·
              refine ⟨22835143684960147425939587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15223429123306764950626391 22835143684960147425939587)
              ·
                refine ⟨34252715527440221138909381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22835143684960147425939587 34252715527440221138909381)
                ·
                  refine ⟨6422384161395041463545509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34252715527440221138909381 6422384161395041463545509)
                  ·
                    refine ⟨1204197030261570274414783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422384161395041463545509 1204197030261570274414783)
                    ·
                      rfl

theorem cell23_7035496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_7035496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035496 prefixEnd_7035496 := by exact prefixLift 7035496
  have htrace : WordTrace (prefixWord ++ tailWord_7035496) baseStart_7035496 baseEnd_7035496 := by
    simpa [prefixWord, tailWord_7035496, baseEnd_7035496] using wordTrace_append hprefix tailTrace_7035496
  have hstable : (prefixWord ++ tailWord_7035496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035496).length < 2 ^ (prefixWord ++ tailWord_7035496).sum := by decide
  have hdescent : baseEnd_7035496 < baseStart_7035496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035503 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 1, 2, 2]
def baseStart_7035503 : Nat := 118140960795 + 7035503 * 2 ^ 59
def prefixEnd_7035503 : Nat := 4983230072969 + 3 ^ 40 * 7035503 * 2
def baseEnd_7035503 : Nat := 3612594685149292295856817

theorem tailTrace_7035503 : CollatzResearch.WordTrace tailWord_7035503 prefixEnd_7035503 3612594685149292295856817 := by
  unfold tailWord_7035503
  simp only [CollatzResearch.WordTrace]
  refine ⟨256605875430581674095775163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171070583620387782730516775 256605875430581674095775163)
  ·
    refine ⟨384908813145872511143662745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256605875430581674095775163 384908813145872511143662745)
    ·
      refine ⟨288681609859404383357747059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384908813145872511143662745 288681609859404383357747059)
      ·
        refine ⟨433022414789106575036620589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288681609859404383357747059 433022414789106575036620589)
        ·
          refine ⟨162383405545914965638732721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433022414789106575036620589 162383405545914965638732721)
          ·
            refine ⟨121787554159436224229049541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162383405545914965638732721 121787554159436224229049541)
            ·
              refine ⟨22835166404894292042946789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121787554159436224229049541 22835166404894292042946789)
              ·
                refine ⟨4281593700917679758052523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22835166404894292042946789 4281593700917679758052523)
                ·
                  refine ⟨6422390551376519637078785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281593700917679758052523 6422390551376519637078785)
                  ·
                    refine ⟨4816792913532389727809089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6422390551376519637078785 4816792913532389727809089)
                    ·
                      refine ⟨3612594685149292295856817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4816792913532389727809089 3612594685149292295856817)
                      ·
                        rfl

theorem cell23_7035503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 2, 2].length) (baseStart_7035503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035503 prefixEnd_7035503 := by exact prefixLift 7035503
  have htrace : WordTrace (prefixWord ++ tailWord_7035503) baseStart_7035503 baseEnd_7035503 := by
    simpa [prefixWord, tailWord_7035503, baseEnd_7035503] using wordTrace_append hprefix tailTrace_7035503
  have hstable : (prefixWord ++ tailWord_7035503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035503).length < 2 ^ (prefixWord ++ tailWord_7035503).sum := by decide
  have hdescent : baseEnd_7035503 < baseStart_7035503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035609 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_7035609 : Nat := 118140960795 + 7035609 * 2 ^ 59
def prefixEnd_7035609 : Nat := 4983230072969 + 3 ^ 40 * 7035609 * 2
def baseEnd_7035609 : Nat := 3612649114098668881131329

theorem tailTrace_7035609 : CollatzResearch.WordTrace tailWord_7035609 prefixEnd_7035609 3612649114098668881131329 := by
  unfold tailWord_7035609
  simp only [CollatzResearch.WordTrace]
  refine ⟨256609741568197654199133881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171073161045465102799422587 256609741568197654199133881)
  ·
    refine ⟨192457306176148240649350411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256609741568197654199133881 192457306176148240649350411)
    ·
      refine ⟨288685959264222360974025617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192457306176148240649350411 288685959264222360974025617)
      ·
        refine ⟨216514469448166770730519213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288685959264222360974025617 216514469448166770730519213)
        ·
          refine ⟨81192926043062539023944705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216514469448166770730519213 81192926043062539023944705)
          ·
            refine ⟨60894694532296904267958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81192926043062539023944705 60894694532296904267958529)
            ·
              refine ⟨45671020899222678200968897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60894694532296904267958529 45671020899222678200968897)
              ·
                refine ⟨34253265674417008650726673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45671020899222678200968897 34253265674417008650726673)
                ·
                  refine ⟨25689949255812756488045005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34253265674417008650726673 25689949255812756488045005)
                  ·
                    refine ⟨9633730970929783683016877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25689949255812756488045005 9633730970929783683016877)
                    ·
                      refine ⟨3612649114098668881131329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9633730970929783683016877 3612649114098668881131329)
                      ·
                        rfl

theorem cell23_7035609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_7035609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035609 prefixEnd_7035609 := by exact prefixLift 7035609
  have htrace : WordTrace (prefixWord ++ tailWord_7035609) baseStart_7035609 baseEnd_7035609 := by
    simpa [prefixWord, tailWord_7035609, baseEnd_7035609] using wordTrace_append hprefix tailTrace_7035609
  have hstable : (prefixWord ++ tailWord_7035609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035609).length < 2 ^ (prefixWord ++ tailWord_7035609).sum := by decide
  have hdescent : baseEnd_7035609 < baseStart_7035609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035629 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_7035629 : Nat := 118140960795 + 7035629 * 2 ^ 59
def prefixEnd_7035629 : Nat := 4983230072969 + 3 ^ 40 * 7035629 * 2
def baseEnd_7035629 : Nat := 1204219794570586267627079

theorem tailTrace_7035629 : CollatzResearch.WordTrace tailWord_7035629 prefixEnd_7035629 1204219794570586267627079 := by
  unfold tailWord_7035629
  simp only [CollatzResearch.WordTrace]
  refine ⟨256610471028125197614861941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171073647352083465076574627 256610471028125197614861941)
  ·
    refine ⟨24057231658886737276393307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256610471028125197614861941 24057231658886737276393307)
    ·
      refine ⟨36085847488330105914589961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24057231658886737276393307 36085847488330105914589961)
      ·
        refine ⟨27064385616247579435942471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36085847488330105914589961 27064385616247579435942471)
        ·
          refine ⟨40596578424371369153913707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27064385616247579435942471 40596578424371369153913707)
          ·
            refine ⟨60894867636557053730870561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40596578424371369153913707 60894867636557053730870561)
            ·
              refine ⟨45671150727417790298152921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60894867636557053730870561 45671150727417790298152921)
              ·
                refine ⟨34253363045563342723614691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45671150727417790298152921 34253363045563342723614691)
                ·
                  refine ⟨51380044568345014085422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34253363045563342723614691 51380044568345014085422037)
                  ·
                    refine ⟨1204219794570586267627079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51380044568345014085422037 1204219794570586267627079)
                    ·
                      rfl

theorem cell23_7035629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_7035629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035629 prefixEnd_7035629 := by exact prefixLift 7035629
  have htrace : WordTrace (prefixWord ++ tailWord_7035629) baseStart_7035629 baseEnd_7035629 := by
    simpa [prefixWord, tailWord_7035629, baseEnd_7035629] using wordTrace_append hprefix tailTrace_7035629
  have hstable : (prefixWord ++ tailWord_7035629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035629).length < 2 ^ (prefixWord ++ tailWord_7035629).sum := by decide
  have hdescent : baseEnd_7035629 < baseStart_7035629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035646 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_7035646 : Nat := 118140960795 + 7035646 * 2 ^ 59
def prefixEnd_7035646 : Nat := 4983230072969 + 3 ^ 40 * 7035646 * 2
def baseEnd_7035646 : Nat := 1204222704294295078789553

theorem tailTrace_7035646 : CollatzResearch.WordTrace tailWord_7035646 prefixEnd_7035646 1204222704294295078789553 := by
  unfold tailWord_7035646
  simp only [CollatzResearch.WordTrace]
  refine ⟨32076386383632951189778849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171074060712709073012153861 32076386383632951189778849)
  ·
    refine ⟨24057289787724713392334137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32076386383632951189778849 24057289787724713392334137)
    ·
      refine ⟨18042967340793535044250603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24057289787724713392334137 18042967340793535044250603)
      ·
        refine ⟨27064451011190302566375905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18042967340793535044250603 27064451011190302566375905)
        ·
          refine ⟨20298338258392726924781929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27064451011190302566375905 20298338258392726924781929)
          ·
            refine ⟨15223753693794545193586447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20298338258392726924781929 15223753693794545193586447)
            ·
              refine ⟨22835630540691817790379671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15223753693794545193586447 22835630540691817790379671)
              ·
                refine ⟨34253445811037726685569507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22835630540691817790379671 34253445811037726685569507)
                ·
                  refine ⟨51380168716556590028354261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34253445811037726685569507 51380168716556590028354261)
                  ·
                    refine ⟨1204222704294295078789553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51380168716556590028354261 1204222704294295078789553)
                    ·
                      rfl

theorem cell23_7035646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_7035646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035646 prefixEnd_7035646 := by exact prefixLift 7035646
  have htrace : WordTrace (prefixWord ++ tailWord_7035646) baseStart_7035646 baseEnd_7035646 := by
    simpa [prefixWord, tailWord_7035646, baseEnd_7035646] using wordTrace_append hprefix tailTrace_7035646
  have hstable : (prefixWord ++ tailWord_7035646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035646).length < 2 ^ (prefixWord ++ tailWord_7035646).sum := by decide
  have hdescent : baseEnd_7035646 < baseStart_7035646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035659 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 7, 4]
def baseStart_7035659 : Nat := 118140960795 + 7035659 * 2 ^ 59
def prefixEnd_7035659 : Nat := 4983230072969 + 3 ^ 40 * 7035659 * 2
def baseEnd_7035659 : Nat := 1204224929377131228502033

theorem tailTrace_7035659 : CollatzResearch.WordTrace tailWord_7035659 prefixEnd_7035659 1204224929377131228502033 := by
  unfold tailWord_7035659
  simp only [CollatzResearch.WordTrace]
  refine ⟨256611565218016512738454031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171074376812011008492302687 256611565218016512738454031)
  ·
    refine ⟨384917347827024769107681047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256611565218016512738454031 384917347827024769107681047)
    ·
      refine ⟨577376021740537153661521571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384917347827024769107681047 577376021740537153661521571)
      ·
        refine ⟨866064032610805730492282357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577376021740537153661521571 866064032610805730492282357)
        ·
          refine ⟨81193503057263037233651471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 866064032610805730492282357 81193503057263037233651471)
          ·
            refine ⟨121790254585894555850477207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81193503057263037233651471 121790254585894555850477207)
            ·
              refine ⟨182685381878841833775715811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121790254585894555850477207 182685381878841833775715811)
              ·
                refine ⟨274028072818262750663573717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182685381878841833775715811 274028072818262750663573717)
                ·
                  refine ⟨6422532956678033218677509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 274028072818262750663573717 6422532956678033218677509)
                  ·
                    refine ⟨1204224929377131228502033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422532956678033218677509 1204224929377131228502033)
                    ·
                      rfl

theorem cell23_7035659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 4].length) (baseStart_7035659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035659 prefixEnd_7035659 := by exact prefixLift 7035659
  have htrace : WordTrace (prefixWord ++ tailWord_7035659) baseStart_7035659 baseEnd_7035659 := by
    simpa [prefixWord, tailWord_7035659, baseEnd_7035659] using wordTrace_append hprefix tailTrace_7035659
  have hstable : (prefixWord ++ tailWord_7035659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035659).length < 2 ^ (prefixWord ++ tailWord_7035659).sum := by decide
  have hdescent : baseEnd_7035659 < baseStart_7035659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035676 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_7035676 : Nat := 118140960795 + 7035676 * 2 ^ 59
def prefixEnd_7035676 : Nat := 4983230072969 + 3 ^ 40 * 7035676 * 2
def baseEnd_7035676 : Nat := 1204227839100840039664507

theorem tailTrace_7035676 : CollatzResearch.WordTrace tailWord_7035676 prefixEnd_7035676 1204227839100840039664507 := by
  unfold tailWord_7035676
  simp only [CollatzResearch.WordTrace]
  refine ⟨128306092629477462320911441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171074790172636616427881921 128306092629477462320911441)
  ·
    refine ⟨96229569472108096740683581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128306092629477462320911441 96229569472108096740683581)
    ·
      refine ⟨36086088552040536277756343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96229569472108096740683581 36086088552040536277756343)
      ·
        refine ⟨54129132828060804416634515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36086088552040536277756343 54129132828060804416634515)
        ·
          refine ⟨81193699242091206624951773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54129132828060804416634515 81193699242091206624951773)
          ·
            refine ⟨30447637215784202484356915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81193699242091206624951773 30447637215784202484356915)
            ·
              refine ⟨45671455823676303726535373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30447637215784202484356915 45671455823676303726535373)
              ·
                refine ⟨17126795933878613897450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45671455823676303726535373 17126795933878613897450765)
                ·
                  refine ⟨6422548475204480211544037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17126795933878613897450765 6422548475204480211544037)
                  ·
                    refine ⟨1204227839100840039664507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422548475204480211544037 1204227839100840039664507)
                    ·
                      rfl

theorem cell23_7035676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_7035676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035676 prefixEnd_7035676 := by exact prefixLift 7035676
  have htrace : WordTrace (prefixWord ++ tailWord_7035676) baseStart_7035676 baseEnd_7035676 := by
    simpa [prefixWord, tailWord_7035676, baseEnd_7035676] using wordTrace_append hprefix tailTrace_7035676
  have hstable : (prefixWord ++ tailWord_7035676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035676).length < 2 ^ (prefixWord ++ tailWord_7035676).sum := by decide
  have hdescent : baseEnd_7035676 < baseStart_7035676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035719 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 5, 5]
def baseStart_7035719 : Nat := 118140960795 + 7035719 * 2 ^ 59
def prefixEnd_7035719 : Nat := 4983230072969 + 3 ^ 40 * 7035719 * 2
def baseEnd_7035719 : Nat := 1204235198990221150251941

theorem tailTrace_7035719 : CollatzResearch.WordTrace tailWord_7035719 prefixEnd_7035719 1204235198990221150251941 := by
  unfold tailWord_7035719
  simp only [CollatzResearch.WordTrace]
  refine ⟨256613753597799142985638211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171075835731866095323758807 256613753597799142985638211)
  ·
    refine ⟨384920630396698714478457317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256613753597799142985638211 384920630396698714478457317)
    ·
      refine ⟨72172618199381008964710747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384920630396698714478457317 72172618199381008964710747)
      ·
        refine ⟨108258927299071513447066121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72172618199381008964710747 108258927299071513447066121)
        ·
          refine ⟨81194195474303635085299591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108258927299071513447066121 81194195474303635085299591)
          ·
            refine ⟨121791293211455452627949387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81194195474303635085299591 121791293211455452627949387)
            ·
              refine ⟨182686939817183178941924081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121791293211455452627949387 182686939817183178941924081)
              ·
                refine ⟨137015204862887384206443061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182686939817183178941924081 137015204862887384206443061)
                ·
                  refine ⟨12845175455895692269354037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137015204862887384206443061 12845175455895692269354037)
                  ·
                    refine ⟨1204235198990221150251941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12845175455895692269354037 1204235198990221150251941)
                    ·
                      rfl

theorem cell23_7035719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_7035719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035719 prefixEnd_7035719 := by exact prefixLift 7035719
  have htrace : WordTrace (prefixWord ++ tailWord_7035719) baseStart_7035719 baseEnd_7035719 := by
    simpa [prefixWord, tailWord_7035719, baseEnd_7035719] using wordTrace_append hprefix tailTrace_7035719
  have hstable : (prefixWord ++ tailWord_7035719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035719).length < 2 ^ (prefixWord ++ tailWord_7035719).sum := by decide
  have hdescent : baseEnd_7035719 < baseStart_7035719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035740 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 6]
def baseStart_7035740 : Nat := 118140960795 + 7035740 * 2 ^ 59
def prefixEnd_7035740 : Nat := 4983230072969 + 3 ^ 40 * 7035740 * 2
def baseEnd_7035740 : Nat := 401412931118267540954803

theorem tailTrace_7035740 : CollatzResearch.WordTrace tailWord_7035740 prefixEnd_7035740 401412931118267540954803 := by
  unfold tailWord_7035740
  simp only [CollatzResearch.WordTrace]
  refine ⟨128307259765361531786076337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171076346353815375714768449 128307259765361531786076337)
  ·
    refine ⟨96230444824021148839557253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128307259765361531786076337 96230444824021148839557253)
    ·
      refine ⟨18043208404503965407416985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96230444824021148839557253 18043208404503965407416985)
      ·
        refine ⟨13532406303377974055562739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18043208404503965407416985 13532406303377974055562739)
        ·
          refine ⟨20298609455066961083344109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13532406303377974055562739 20298609455066961083344109)
          ·
            refine ⟨7611978545650110406254041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20298609455066961083344109 7611978545650110406254041)
            ·
              refine ⟨5708983909237582804690531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611978545650110406254041 5708983909237582804690531)
              ·
                refine ⟨8563475863856374207035797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708983909237582804690531 8563475863856374207035797)
                ·
                  refine ⟨401412931118267540954803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8563475863856374207035797 401412931118267540954803)
                  ·
                    rfl

theorem cell23_7035740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_7035740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035740 prefixEnd_7035740 := by exact prefixLift 7035740
  have htrace : WordTrace (prefixWord ++ tailWord_7035740) baseStart_7035740 baseEnd_7035740 := by
    simpa [prefixWord, tailWord_7035740, baseEnd_7035740] using wordTrace_append hprefix tailTrace_7035740
  have hstable : (prefixWord ++ tailWord_7035740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035740).length < 2 ^ (prefixWord ++ tailWord_7035740).sum := by decide
  have hdescent : baseEnd_7035740 < baseStart_7035740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035756 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_7035756 : Nat := 118140960795 + 7035756 * 2 ^ 59
def prefixEnd_7035756 : Nat := 4983230072969 + 3 ^ 40 * 7035756 * 2
def baseEnd_7035756 : Nat := 3612724595754879805993153

theorem tailTrace_7035756 : CollatzResearch.WordTrace tailWord_7035756 prefixEnd_7035756 3612724595754879805993153 := by
  unfold tailWord_7035756
  simp only [CollatzResearch.WordTrace]
  refine ⟨128307551549332549152367561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171076735399110065536490081 128307551549332549152367561)
  ·
    refine ⟨96230663661999411864275671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128307551549332549152367561 96230663661999411864275671)
    ·
      refine ⟨144345995492999117796413507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96230663661999411864275671 144345995492999117796413507)
      ·
        refine ⟨216518993239498676694620261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144345995492999117796413507 216518993239498676694620261)
        ·
          refine ⟨40597311232406001880241299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216518993239498676694620261 40597311232406001880241299)
          ·
            refine ⟨60895966848609002820361949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40597311232406001880241299 60895966848609002820361949)
            ·
              refine ⟨22835987568228376057635731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60895966848609002820361949 22835987568228376057635731)
              ·
                refine ⟨34253981352342564086453597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22835987568228376057635731 34253981352342564086453597)
                ·
                  refine ⟨12845243007128461532420099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34253981352342564086453597 12845243007128461532420099)
                  ·
                    refine ⟨19267864510692692298630149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12845243007128461532420099 19267864510692692298630149)
                    ·
                      refine ⟨3612724595754879805993153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19267864510692692298630149 3612724595754879805993153)
                      ·
                        rfl

theorem cell23_7035756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_7035756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035756 prefixEnd_7035756 := by exact prefixLift 7035756
  have htrace : WordTrace (prefixWord ++ tailWord_7035756) baseStart_7035756 baseEnd_7035756 := by
    simpa [prefixWord, tailWord_7035756, baseEnd_7035756] using wordTrace_append hprefix tailTrace_7035756
  have hstable : (prefixWord ++ tailWord_7035756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035756).length < 2 ^ (prefixWord ++ tailWord_7035756).sum := by decide
  have hdescent : baseEnd_7035756 < baseStart_7035756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035759 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_7035759 : Nat := 118140960795 + 7035759 * 2 ^ 59
def prefixEnd_7035759 : Nat := 4983230072969 + 3 ^ 40 * 7035759 * 2
def baseEnd_7035759 : Nat := 3612726136196843294255639

theorem tailTrace_7035759 : CollatzResearch.WordTrace tailWord_7035759 prefixEnd_7035759 3612726136196843294255639 := by
  unfold tailWord_7035759
  simp only [CollatzResearch.WordTrace]
  refine ⟨256615212517654229817094331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171076808345102819878062887 256615212517654229817094331)
  ·
    refine ⟨384922818776481344725641497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256615212517654229817094331 384922818776481344725641497)
    ·
      refine ⟨288692114082361008544231123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384922818776481344725641497 288692114082361008544231123)
      ·
        refine ⟨433038171123541512816346685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288692114082361008544231123 433038171123541512816346685)
        ·
          refine ⟨162389314171328067306130007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433038171123541512816346685 162389314171328067306130007)
          ·
            refine ⟨243583971256992100959195011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162389314171328067306130007 243583971256992100959195011)
            ·
              refine ⟨365375956885488151438792517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243583971256992100959195011 365375956885488151438792517)
              ·
                refine ⟨68507991916029028394773597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365375956885488151438792517 68507991916029028394773597)
                ·
                  refine ⟨25690496968510885648040099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68507991916029028394773597 25690496968510885648040099)
                  ·
                    refine ⟨38535745452766328472060149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25690496968510885648040099 38535745452766328472060149)
                    ·
                      refine ⟨3612726136196843294255639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38535745452766328472060149 3612726136196843294255639)
                      ·
                        rfl

theorem cell23_7035759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_7035759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035759 prefixEnd_7035759 := by exact prefixLift 7035759
  have htrace : WordTrace (prefixWord ++ tailWord_7035759) baseStart_7035759 baseEnd_7035759 := by
    simpa [prefixWord, tailWord_7035759, baseEnd_7035759] using wordTrace_append hprefix tailTrace_7035759
  have hstable : (prefixWord ++ tailWord_7035759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035759).length < 2 ^ (prefixWord ++ tailWord_7035759).sum := by decide
  have hdescent : baseEnd_7035759 < baseStart_7035759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035778 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7035778 : Nat := 118140960795 + 7035778 * 2 ^ 59
def prefixEnd_7035778 : Nat := 4983230072969 + 3 ^ 40 * 7035778 * 2
def baseEnd_7035778 : Nat := 1204245297443092906639351

theorem tailTrace_7035778 : CollatzResearch.WordTrace tailWord_7035778 prefixEnd_7035778 1204245297443092906639351 := by
  unfold tailWord_7035778
  simp only [CollatzResearch.WordTrace]
  refine ⟨64153976376146349015508997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171077270336390264041357325 64153976376146349015508997)
  ·
    refine ⟨12028870570527440440407937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64153976376146349015508997 12028870570527440440407937)
    ·
      refine ⟨9021652927895580330305953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12028870570527440440407937 9021652927895580330305953)
      ·
        refine ⟨6766239695921685247729465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9021652927895580330305953 6766239695921685247729465)
        ·
          refine ⟨5074679771941263935797099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6766239695921685247729465 5074679771941263935797099)
          ·
            refine ⟨7612019657911895903695649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074679771941263935797099 7612019657911895903695649)
            ·
              refine ⟨5709014743433921927771737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612019657911895903695649 5709014743433921927771737)
              ·
                refine ⟨4281761057575441445828803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709014743433921927771737 4281761057575441445828803)
                ·
                  refine ⟨6422641586363162168743205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281761057575441445828803 6422641586363162168743205)
                  ·
                    refine ⟨1204245297443092906639351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422641586363162168743205 1204245297443092906639351)
                    ·
                      rfl

theorem cell23_7035778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7035778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035778 prefixEnd_7035778 := by exact prefixLift 7035778
  have htrace : WordTrace (prefixWord ++ tailWord_7035778) baseStart_7035778 baseEnd_7035778 := by
    simpa [prefixWord, tailWord_7035778, baseEnd_7035778] using wordTrace_append hprefix tailTrace_7035778
  have hstable : (prefixWord ++ tailWord_7035778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035778).length < 2 ^ (prefixWord ++ tailWord_7035778).sum := by decide
  have hdescent : baseEnd_7035778 < baseStart_7035778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035783 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 2, 4]
def baseStart_7035783 : Nat := 118140960795 + 7035783 * 2 ^ 59
def prefixEnd_7035783 : Nat := 4983230072969 + 3 ^ 40 * 7035783 * 2
def baseEnd_7035783 : Nat := 1204246153244183733451843

theorem tailTrace_7035783 : CollatzResearch.WordTrace tailWord_7035783 prefixEnd_7035783 1204246153244183733451843 := by
  unfold tailWord_7035783
  simp only [CollatzResearch.WordTrace]
  refine ⟨256616087869567281915968003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171077391913044854610645335 256616087869567281915968003)
  ·
    refine ⟨384924131804350922873952005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256616087869567281915968003 384924131804350922873952005)
    ·
      refine ⟨72173274713315798038866001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384924131804350922873952005 72173274713315798038866001)
      ·
        refine ⟨54129956034986848529149501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72173274713315798038866001 54129956034986848529149501)
        ·
          refine ⟨20298733513120068198431063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54129956034986848529149501 20298733513120068198431063)
          ·
            refine ⟨30448100269680102297646595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20298733513120068198431063 30448100269680102297646595)
            ·
              refine ⟨45672150404520153446469893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30448100269680102297646595 45672150404520153446469893)
              ·
                refine ⟨8563528200847528771213105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45672150404520153446469893 8563528200847528771213105)
                ·
                  refine ⟨6422646150635646578409829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8563528200847528771213105 6422646150635646578409829)
                  ·
                    refine ⟨1204246153244183733451843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422646150635646578409829 1204246153244183733451843)
                    ·
                      rfl

theorem cell23_7035783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_7035783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035783 prefixEnd_7035783 := by exact prefixLift 7035783
  have htrace : WordTrace (prefixWord ++ tailWord_7035783) baseStart_7035783 baseEnd_7035783 := by
    simpa [prefixWord, tailWord_7035783, baseEnd_7035783] using wordTrace_append hprefix tailTrace_7035783
  have hstable : (prefixWord ++ tailWord_7035783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035783).length < 2 ^ (prefixWord ++ tailWord_7035783).sum := by decide
  have hdescent : baseEnd_7035783 < baseStart_7035783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035784 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_7035784 : Nat := 118140960795 + 7035784 * 2 ^ 59
def prefixEnd_7035784 : Nat := 4983230072969 + 3 ^ 40 * 7035784 * 2
def baseEnd_7035784 : Nat := 3612738973213205696443025

theorem tailTrace_7035784 : CollatzResearch.WordTrace tailWord_7035784 prefixEnd_7035784 3612738973213205696443025 := by
  unfold tailWord_7035784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128308062171281829543377203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171077416228375772724502937 128308062171281829543377203)
  ·
    refine ⟨192462093256922744315065805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128308062171281829543377203 192462093256922744315065805)
    ·
      refine ⟨72173284971346029118149677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192462093256922744315065805 72173284971346029118149677)
      ·
        refine ⟨27064981864254760919306129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72173284971346029118149677 27064981864254760919306129)
        ·
          refine ⟨20298736398191070689479597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27064981864254760919306129 20298736398191070689479597)
          ·
            refine ⟨7612026149321651508554849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20298736398191070689479597 7612026149321651508554849)
            ·
              refine ⟨5709019611991238631416137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612026149321651508554849 5709019611991238631416137)
              ·
                refine ⟨4281764708993428973562103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709019611991238631416137 4281764708993428973562103)
                ·
                  refine ⟨6422647063490143460343155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281764708993428973562103 6422647063490143460343155)
                  ·
                    refine ⟨9633970595235215190514733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422647063490143460343155 9633970595235215190514733)
                    ·
                      refine ⟨3612738973213205696443025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9633970595235215190514733 3612738973213205696443025)
                      ·
                        rfl

theorem cell23_7035784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_7035784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035784 prefixEnd_7035784 := by exact prefixLift 7035784
  have htrace : WordTrace (prefixWord ++ tailWord_7035784) baseStart_7035784 baseEnd_7035784 := by
    simpa [prefixWord, tailWord_7035784, baseEnd_7035784] using wordTrace_append hprefix tailTrace_7035784
  have hstable : (prefixWord ++ tailWord_7035784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035784).length < 2 ^ (prefixWord ++ tailWord_7035784).sum := by decide
  have hdescent : baseEnd_7035784 < baseStart_7035784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035819 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_7035819 : Nat := 118140960795 + 7035819 * 2 ^ 59
def prefixEnd_7035819 : Nat := 4983230072969 + 3 ^ 40 * 7035819 * 2
def baseEnd_7035819 : Nat := 3612756945036113059505363

theorem tailTrace_7035819 : CollatzResearch.WordTrace tailWord_7035819 prefixEnd_7035819 3612756945036113059505363 := by
  unfold tailWord_7035819
  simp only [CollatzResearch.WordTrace]
  refine ⟨256617400897436860064278511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171078267264957906709519007 256617400897436860064278511)
  ·
    refine ⟨384926101346155290096417767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256617400897436860064278511 384926101346155290096417767)
    ·
      refine ⟨577389152019232935144626651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384926101346155290096417767 577389152019232935144626651)
      ·
        refine ⟨866083728028849402716939977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577389152019232935144626651 866083728028849402716939977)
        ·
          refine ⟨649562796021637052037704983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866083728028849402716939977 649562796021637052037704983)
          ·
            refine ⟨974344194032455578056557475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649562796021637052037704983 974344194032455578056557475)
            ·
              refine ⟨1461516291048683367084836213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974344194032455578056557475 1461516291048683367084836213)
              ·
                refine ⟨137017152285814065664203395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461516291048683367084836213 137017152285814065664203395)
                ·
                  refine ⟨205525728428721098496305093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137017152285814065664203395 205525728428721098496305093)
                  ·
                    refine ⟨38536074080385205968057205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205525728428721098496305093 38536074080385205968057205)
                    ·
                      refine ⟨3612756945036113059505363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38536074080385205968057205 3612756945036113059505363)
                      ·
                        rfl

theorem cell23_7035819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_7035819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035819 prefixEnd_7035819 := by exact prefixLift 7035819
  have htrace : WordTrace (prefixWord ++ tailWord_7035819) baseStart_7035819 baseEnd_7035819 := by
    simpa [prefixWord, tailWord_7035819, baseEnd_7035819] using wordTrace_append hprefix tailTrace_7035819
  have hstable : (prefixWord ++ tailWord_7035819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035819).length < 2 ^ (prefixWord ++ tailWord_7035819).sum := by decide
  have hdescent : baseEnd_7035819 < baseStart_7035819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035840 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3]
def baseStart_7035840 : Nat := 118140960795 + 7035840 * 2 ^ 59
def prefixEnd_7035840 : Nat := 4983230072969 + 3 ^ 40 * 7035840 * 2
def baseEnd_7035840 : Nat := 3612767728129857477342767

theorem tailTrace_7035840 : CollatzResearch.WordTrace tailWord_7035840 prefixEnd_7035840 3612767728129857477342767 := by
  unfold tailWord_7035840
  simp only [CollatzResearch.WordTrace]
  refine ⟨128309083415180390325396487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171078777886907187100528649 128309083415180390325396487)
  ·
    refine ⟨192463625122770585488094731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128309083415180390325396487 192463625122770585488094731)
    ·
      refine ⟨288695437684155878232142097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192463625122770585488094731 288695437684155878232142097)
      ·
        refine ⟨216521578263116908674106573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288695437684155878232142097 216521578263116908674106573)
        ·
          refine ⟨81195591848668840752789965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216521578263116908674106573 81195591848668840752789965)
          ·
            refine ⟨30448346943250815282296237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81195591848668840752789965 30448346943250815282296237)
            ·
              refine ⟨11418130103719055730861089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30448346943250815282296237 11418130103719055730861089)
              ·
                refine ⟨8563597577789291798145817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11418130103719055730861089 8563597577789291798145817)
                ·
                  refine ⟨6422698183341968848609363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8563597577789291798145817 6422698183341968848609363)
                  ·
                    refine ⟨9634047275012953272914045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422698183341968848609363 9634047275012953272914045)
                    ·
                      refine ⟨3612767728129857477342767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634047275012953272914045 3612767728129857477342767)
                      ·
                        rfl

theorem cell23_7035840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_7035840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035840 prefixEnd_7035840 := by exact prefixLift 7035840
  have htrace : WordTrace (prefixWord ++ tailWord_7035840) baseStart_7035840 baseEnd_7035840 := by
    simpa [prefixWord, tailWord_7035840, baseEnd_7035840] using wordTrace_append hprefix tailTrace_7035840
  have hstable : (prefixWord ++ tailWord_7035840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035840).length < 2 ^ (prefixWord ++ tailWord_7035840).sum := by decide
  have hdescent : baseEnd_7035840 < baseStart_7035840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035859 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_7035859 : Nat := 118140960795 + 7035859 * 2 ^ 59
def prefixEnd_7035859 : Nat := 4983230072969 + 3 ^ 40 * 7035859 * 2
def baseEnd_7035859 : Nat := 3612777484262292903005179

theorem tailTrace_7035859 : CollatzResearch.WordTrace tailWord_7035859 prefixEnd_7035859 3612777484262292903005179 := by
  unfold tailWord_7035859
  simp only [CollatzResearch.WordTrace]
  refine ⟨256618859817291946895734631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171079239878194631263823087 256618859817291946895734631)
  ·
    refine ⟨384928289725937920343601947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256618859817291946895734631 384928289725937920343601947)
    ·
      refine ⟨577392434588906880515402921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384928289725937920343601947 577392434588906880515402921)
      ·
        refine ⟨433044325941680160386552191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577392434588906880515402921 433044325941680160386552191)
        ·
          refine ⟨649566488912520240579828287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433044325941680160386552191 649566488912520240579828287)
          ·
            refine ⟨974349733368780360869742431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649566488912520240579828287 974349733368780360869742431)
            ·
              refine ⟨1461524600053170541304613647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974349733368780360869742431 1461524600053170541304613647)
              ·
                refine ⟨2192286900079755811956920471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461524600053170541304613647 2192286900079755811956920471)
                ·
                  refine ⟨3288430350119633717935380707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192286900079755811956920471 3288430350119633717935380707)
                  ·
                    refine ⟨4932645525179450576903071061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288430350119633717935380707 4932645525179450576903071061)
                    ·
                      refine ⟨3612777484262292903005179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 4932645525179450576903071061 3612777484262292903005179)
                      ·
                        rfl

theorem cell23_7035859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_7035859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035859 prefixEnd_7035859 := by exact prefixLift 7035859
  have htrace : WordTrace (prefixWord ++ tailWord_7035859) baseStart_7035859 baseEnd_7035859 := by
    simpa [prefixWord, tailWord_7035859, baseEnd_7035859] using wordTrace_append hprefix tailTrace_7035859
  have hstable : (prefixWord ++ tailWord_7035859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035859).length < 2 ^ (prefixWord ++ tailWord_7035859).sum := by decide
  have hdescent : baseEnd_7035859 < baseStart_7035859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035863 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_7035863 : Nat := 118140960795 + 7035863 * 2 ^ 59
def prefixEnd_7035863 : Nat := 4983230072969 + 3 ^ 40 * 7035863 * 2
def baseEnd_7035863 : Nat := 3612779538184910887355161

theorem tailTrace_7035863 : CollatzResearch.WordTrace tailWord_7035863 prefixEnd_7035863 3612779538184910887355161 := by
  unfold tailWord_7035863
  simp only [CollatzResearch.WordTrace]
  refine ⟨256619005709277455578880243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171079337139518303719253495 256619005709277455578880243)
  ·
    refine ⟨384928508563916183368320365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256619005709277455578880243 384928508563916183368320365)
    ·
      refine ⟨144348190711468568763120137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384928508563916183368320365 144348190711468568763120137)
      ·
        refine ⟨108261143033601426572340103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144348190711468568763120137 108261143033601426572340103)
        ·
          refine ⟨162391714550402139858510155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108261143033601426572340103 162391714550402139858510155)
          ·
            refine ⟨243587571825603209787765233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162391714550402139858510155 243587571825603209787765233)
            ·
              refine ⟨182690678869202407340823925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243587571825603209787765233 182690678869202407340823925)
              ·
                refine ⟨17127251143987725688202243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182690678869202407340823925 17127251143987725688202243)
                ·
                  refine ⟨25690876715981588532303365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17127251143987725688202243 25690876715981588532303365)
                  ·
                    refine ⟨4817039384246547849806881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25690876715981588532303365 4817039384246547849806881)
                    ·
                      refine ⟨3612779538184910887355161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817039384246547849806881 3612779538184910887355161)
                      ·
                        rfl

theorem cell23_7035863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_7035863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035863 prefixEnd_7035863 := by exact prefixLift 7035863
  have htrace : WordTrace (prefixWord ++ tailWord_7035863) baseStart_7035863 baseEnd_7035863 := by
    simpa [prefixWord, tailWord_7035863, baseEnd_7035863] using wordTrace_append hprefix tailTrace_7035863
  have hstable : (prefixWord ++ tailWord_7035863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035863).length < 2 ^ (prefixWord ++ tailWord_7035863).sum := by decide
  have hdescent : baseEnd_7035863 < baseStart_7035863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035876 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_7035876 : Nat := 118140960795 + 7035876 * 2 ^ 59
def prefixEnd_7035876 : Nat := 4983230072969 + 3 ^ 40 * 7035876 * 2
def baseEnd_7035876 : Nat := 3612786213433419336492601

theorem tailTrace_7035876 : CollatzResearch.WordTrace tailWord_7035876 prefixEnd_7035876 3612786213433419336492601 := by
  unfold tailWord_7035876
  simp only [CollatzResearch.WordTrace]
  refine ⟨128309739929115179399551741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171079653238820239199402321 128309739929115179399551741)
  ·
    refine ⟨48116152473418192274831903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128309739929115179399551741 48116152473418192274831903)
    ·
      refine ⟨72174228710127288412247855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48116152473418192274831903 72174228710127288412247855)
      ·
        refine ⟨108261343065190932618371783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72174228710127288412247855 108261343065190932618371783)
        ·
          refine ⟨162392014597786398927557675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108261343065190932618371783 162392014597786398927557675)
          ·
            refine ⟨243588021896679598391336513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162392014597786398927557675 243588021896679598391336513)
            ·
              refine ⟨182691016422509698793502385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243588021896679598391336513 182691016422509698793502385)
              ·
                refine ⟨137018262316882274095126789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182691016422509698793502385 137018262316882274095126789)
                ·
                  refine ⟨25690924184415426392836273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137018262316882274095126789 25690924184415426392836273)
                  ·
                    refine ⟨19268193138311569794627205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25690924184415426392836273 19268193138311569794627205)
                    ·
                      refine ⟨3612786213433419336492601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19268193138311569794627205 3612786213433419336492601)
                      ·
                        rfl

theorem cell23_7035876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_7035876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035876 prefixEnd_7035876 := by exact prefixLift 7035876
  have htrace : WordTrace (prefixWord ++ tailWord_7035876) baseStart_7035876 baseEnd_7035876 := by
    simpa [prefixWord, tailWord_7035876, baseEnd_7035876] using wordTrace_append hprefix tailTrace_7035876
  have hstable : (prefixWord ++ tailWord_7035876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035876).length < 2 ^ (prefixWord ++ tailWord_7035876).sum := by decide
  have hdescent : baseEnd_7035876 < baseStart_7035876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035880 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7035880 : Nat := 118140960795 + 7035880 * 2 ^ 59
def prefixEnd_7035880 : Nat := 4983230072969 + 3 ^ 40 * 7035880 * 2
def baseEnd_7035880 : Nat := 3612788267356037320842583

theorem tailTrace_7035880 : CollatzResearch.WordTrace tailWord_7035880 prefixEnd_7035880 3612788267356037320842583 := by
  unfold tailWord_7035880
  simp only [CollatzResearch.WordTrace]
  refine ⟨128309812875107933741124547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171079750500143911654832729 128309812875107933741124547)
  ·
    refine ⟨192464719312661900611686821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128309812875107933741124547 192464719312661900611686821)
    ·
      refine ⟨36087134871124106364691279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192464719312661900611686821 36087134871124106364691279)
      ·
        refine ⟨54130702306686159547036919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36087134871124106364691279 54130702306686159547036919)
        ·
          refine ⟨81196053460029239320555379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54130702306686159547036919 81196053460029239320555379)
          ·
            refine ⟨121794080190043858980833069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81196053460029239320555379 121794080190043858980833069)
            ·
              refine ⟨45672780071266447117812401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121794080190043858980833069 45672780071266447117812401)
              ·
                refine ⟨34254585053449835338359301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45672780071266447117812401 34254585053449835338359301)
                ·
                  refine ⟨6422734697521844125942369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34254585053449835338359301 6422734697521844125942369)
                  ·
                    refine ⟨4817051023141383094456777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6422734697521844125942369 4817051023141383094456777)
                    ·
                      refine ⟨3612788267356037320842583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817051023141383094456777 3612788267356037320842583)
                      ·
                        rfl

theorem cell23_7035880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7035880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035880 prefixEnd_7035880 := by exact prefixLift 7035880
  have htrace : WordTrace (prefixWord ++ tailWord_7035880) baseStart_7035880 baseEnd_7035880 := by
    simpa [prefixWord, tailWord_7035880, baseEnd_7035880] using wordTrace_append hprefix tailTrace_7035880
  have hstable : (prefixWord ++ tailWord_7035880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035880).length < 2 ^ (prefixWord ++ tailWord_7035880).sum := by decide
  have hdescent : baseEnd_7035880 < baseStart_7035880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035892 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7035892 : Nat := 118140960795 + 7035892 * 2 ^ 59
def prefixEnd_7035892 : Nat := 4983230072969 + 3 ^ 40 * 7035892 * 2
def baseEnd_7035892 : Nat := 3612794429123891273892529

theorem tailTrace_7035892 : CollatzResearch.WordTrace tailWord_7035892 prefixEnd_7035892 3612794429123891273892529 := by
  unfold tailWord_7035892
  simp only [CollatzResearch.WordTrace]
  refine ⟨128310031713086196765842965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171080042284114929021123953 128310031713086196765842965)
  ·
    refine ⟨6014532736550915473398889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128310031713086196765842965 6014532736550915473398889)
    ·
      refine ⟨4510899552413186605049167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6014532736550915473398889 4510899552413186605049167)
      ·
        refine ⟨6766349328619779907573751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4510899552413186605049167 6766349328619779907573751)
        ·
          refine ⟨10149523992929669861360627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6766349328619779907573751 10149523992929669861360627)
          ·
            refine ⟨15224285989394504792040941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10149523992929669861360627 15224285989394504792040941)
            ·
              refine ⟨5709107246022939297015353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15224285989394504792040941 5709107246022939297015353)
              ·
                refine ⟨4281830434517204472761515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709107246022939297015353 4281830434517204472761515)
                ·
                  refine ⟨6422745651775806709142273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281830434517204472761515 6422745651775806709142273)
                  ·
                    refine ⟨4817059238831855031856705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6422745651775806709142273 4817059238831855031856705)
                    ·
                      refine ⟨3612794429123891273892529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817059238831855031856705 3612794429123891273892529)
                      ·
                        rfl

theorem cell23_7035892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7035892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035892 prefixEnd_7035892 := by exact prefixLift 7035892
  have htrace : WordTrace (prefixWord ++ tailWord_7035892) baseStart_7035892 baseEnd_7035892 := by
    simpa [prefixWord, tailWord_7035892, baseEnd_7035892] using wordTrace_append hprefix tailTrace_7035892
  have hstable : (prefixWord ++ tailWord_7035892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035892).length < 2 ^ (prefixWord ++ tailWord_7035892).sum := by decide
  have hdescent : baseEnd_7035892 < baseStart_7035892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035914 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_7035914 : Nat := 118140960795 + 7035914 * 2 ^ 59
def prefixEnd_7035914 : Nat := 4983230072969 + 3 ^ 40 * 7035914 * 2
def baseEnd_7035914 : Nat := 3612805725698290187817427

theorem tailTrace_7035914 : CollatzResearch.WordTrace tailWord_7035914 prefixEnd_7035914 3612805725698290187817427 := by
  unfold tailWord_7035914
  simp only [CollatzResearch.WordTrace]
  refine ⟨64155216458023172822246699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171080577221395127525991197 64155216458023172822246699)
  ·
    refine ⟨96232824687034759233370049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64155216458023172822246699 96232824687034759233370049)
    ·
      refine ⟨72174618515276069425027537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96232824687034759233370049 72174618515276069425027537)
      ·
        refine ⟨54130963886457052068770653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72174618515276069425027537 54130963886457052068770653)
        ·
          refine ⟨20299111457421394525788995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54130963886457052068770653 20299111457421394525788995)
          ·
            refine ⟨30448667186132091788683493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20299111457421394525788995 30448667186132091788683493)
            ·
              refine ⟨5709125097399767210378155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30448667186132091788683493 5709125097399767210378155)
              ·
                refine ⟨8563687646099650815567233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709125097399767210378155 8563687646099650815567233)
                ·
                  refine ⟨6422765734574738111675425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8563687646099650815567233 6422765734574738111675425)
                  ·
                    refine ⟨4817074300931053583756569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6422765734574738111675425 4817074300931053583756569)
                    ·
                      refine ⟨3612805725698290187817427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817074300931053583756569 3612805725698290187817427)
                      ·
                        rfl

theorem cell23_7035914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_7035914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035914 prefixEnd_7035914 := by exact prefixLift 7035914
  have htrace : WordTrace (prefixWord ++ tailWord_7035914) baseStart_7035914 baseEnd_7035914 := by
    simpa [prefixWord, tailWord_7035914, baseEnd_7035914] using wordTrace_append hprefix tailTrace_7035914
  have hstable : (prefixWord ++ tailWord_7035914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035914).length < 2 ^ (prefixWord ++ tailWord_7035914).sum := by decide
  have hdescent : baseEnd_7035914 < baseStart_7035914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035953 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7035953 : Nat := 118140960795 + 7035953 * 2 ^ 59
def prefixEnd_7035953 : Nat := 4983230072969 + 3 ^ 40 * 7035953 * 2
def baseEnd_7035953 : Nat := 3612825751443815535229747

theorem tailTrace_7035953 : CollatzResearch.WordTrace tailWord_7035953 prefixEnd_7035953 3612825751443815535229747 := by
  unfold tailWord_7035953
  simp only [CollatzResearch.WordTrace]
  refine ⟨256622288278951400949656513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171081525519300933966437675 256622288278951400949656513)
  ·
    refine ⟨192466716209213550712242385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256622288278951400949656513 192466716209213550712242385)
    ·
      refine ⟨144350037156910163034181789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192466716209213550712242385 144350037156910163034181789)
      ·
        refine ⟨54131263933841311137818171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144350037156910163034181789 54131263933841311137818171)
        ·
          refine ⟨81196895900761966706727257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54131263933841311137818171 81196895900761966706727257)
          ·
            refine ⟨60897671925571475030045443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81196895900761966706727257 60897671925571475030045443)
            ·
              refine ⟨91346507888357212545068165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60897671925571475030045443 91346507888357212545068165)
              ·
                refine ⟨17127470229066977352200281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91346507888357212545068165 17127470229066977352200281)
                ·
                  refine ⟨12845602671800233014150211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17127470229066977352200281 12845602671800233014150211)
                  ·
                    refine ⟨19268404007700349521225317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12845602671800233014150211 19268404007700349521225317)
                    ·
                      refine ⟨3612825751443815535229747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19268404007700349521225317 3612825751443815535229747)
                      ·
                        rfl

theorem cell23_7035953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7035953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035953 prefixEnd_7035953 := by exact prefixLift 7035953
  have htrace : WordTrace (prefixWord ++ tailWord_7035953) baseStart_7035953 baseEnd_7035953 := by
    simpa [prefixWord, tailWord_7035953, baseEnd_7035953] using wordTrace_append hprefix tailTrace_7035953
  have hstable : (prefixWord ++ tailWord_7035953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035953).length < 2 ^ (prefixWord ++ tailWord_7035953).sum := by decide
  have hdescent : baseEnd_7035953 < baseStart_7035953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7035973 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_7035973 : Nat := 118140960795 + 7035973 * 2 ^ 59
def prefixEnd_7035973 : Nat := 4983230072969 + 3 ^ 40 * 7035973 * 2
def baseEnd_7035973 : Nat := 3612836021056905456979655

theorem tailTrace_7035973 : CollatzResearch.WordTrace tailWord_7035973 prefixEnd_7035973 3612836021056905456979655 := by
  unfold tailWord_7035973
  simp only [CollatzResearch.WordTrace]
  refine ⟨256623017738878944365384573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171082011825919296243589715 256623017738878944365384573)
  ·
    refine ⟨96233631652079604137019215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256623017738878944365384573 96233631652079604137019215)
    ·
      refine ⟨144350447478119406205528823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96233631652079604137019215 144350447478119406205528823)
      ·
        refine ⟨216525671217179109308293235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144350447478119406205528823 216525671217179109308293235)
        ·
          refine ⟨324788506825768663962439853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216525671217179109308293235 324788506825768663962439853)
          ·
            refine ⟨121795690059663248985914945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324788506825768663962439853 121795690059663248985914945)
            ·
              refine ⟨91346767544747436739436209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121795690059663248985914945 91346767544747436739436209)
              ·
                refine ⟨68510075658560577554577157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91346767544747436739436209 68510075658560577554577157)
                ·
                  refine ⟨12845639185980108291483217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68510075658560577554577157 12845639185980108291483217)
                  ·
                    refine ⟨9634229389485081218612413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12845639185980108291483217 9634229389485081218612413)
                    ·
                      refine ⟨3612836021056905456979655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634229389485081218612413 3612836021056905456979655)
                      ·
                        rfl

theorem cell23_7035973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_7035973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7035973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7035973 prefixEnd_7035973 := by exact prefixLift 7035973
  have htrace : WordTrace (prefixWord ++ tailWord_7035973) baseStart_7035973 baseEnd_7035973 := by
    simpa [prefixWord, tailWord_7035973, baseEnd_7035973] using wordTrace_append hprefix tailTrace_7035973
  have hstable : (prefixWord ++ tailWord_7035973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7035973).length < 2 ^ (prefixWord ++ tailWord_7035973).sum := by decide
  have hdescent : baseEnd_7035973 < baseStart_7035973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7035973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036010 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_7036010 : Nat := 118140960795 + 7036010 * 2 ^ 59
def prefixEnd_7036010 : Nat := 4983230072969 + 3 ^ 40 * 7036010 * 2
def baseEnd_7036010 : Nat := 401428335537902423579665

theorem tailTrace_7036010 : CollatzResearch.WordTrace tailWord_7036010 prefixEnd_7036010 401428335537902423579665 := by
  unfold tailWord_7036010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64156091809936224921120371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171082911493163266456320989 64156091809936224921120371)
  ·
    refine ⟨96234137714904337381680557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64156091809936224921120371 96234137714904337381680557)
    ·
      refine ⟨36087801643089126518130209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96234137714904337381680557 36087801643089126518130209)
      ·
        refine ⟨27065851232316844888597657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36087801643089126518130209 27065851232316844888597657)
        ·
          refine ⟨20299388424237633666448243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27065851232316844888597657 20299388424237633666448243)
          ·
            refine ⟨30449082636356450499672365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20299388424237633666448243 30449082636356450499672365)
            ·
              refine ⟨11418405988633668937377137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30449082636356450499672365 11418405988633668937377137)
              ·
                refine ⟨8563804491475251703032853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11418405988633668937377137 8563804491475251703032853)
                ·
                  refine ⟨401428335537902423579665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8563804491475251703032853 401428335537902423579665)
                  ·
                    rfl

theorem cell23_7036010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_7036010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036010 prefixEnd_7036010 := by exact prefixLift 7036010
  have htrace : WordTrace (prefixWord ++ tailWord_7036010) baseStart_7036010 baseEnd_7036010 := by
    simpa [prefixWord, tailWord_7036010, baseEnd_7036010] using wordTrace_append hprefix tailTrace_7036010
  have hstable : (prefixWord ++ tailWord_7036010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036010).length < 2 ^ (prefixWord ++ tailWord_7036010).sum := by decide
  have hdescent : baseEnd_7036010 < baseStart_7036010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036013 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7036013 : Nat := 118140960795 + 7036013 * 2 ^ 59
def prefixEnd_7036013 : Nat := 4983230072969 + 3 ^ 40 * 7036013 * 2
def baseEnd_7036013 : Nat := 3612856560283085300479471

theorem tailTrace_7036013 : CollatzResearch.WordTrace tailWord_7036013 prefixEnd_7036013 3612856560283085300479471 := by
  unfold tailWord_7036013
  simp only [CollatzResearch.WordTrace]
  refine ⟨256624476658734031196840693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171082984439156020797893795 256624476658734031196840693)
  ·
    refine ⟨24058544686756315424703815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256624476658734031196840693 24058544686756315424703815)
    ·
      refine ⟨36087817030134473137055723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24058544686756315424703815 36087817030134473137055723)
      ·
        refine ⟨54131725545201709705583585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36087817030134473137055723 54131725545201709705583585)
        ·
          refine ⟨40598794158901282279187689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54131725545201709705583585 40598794158901282279187689)
          ·
            refine ⟨30449095619175961709390767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40598794158901282279187689 30449095619175961709390767)
            ·
              refine ⟨45673643428763942564086151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30449095619175961709390767 45673643428763942564086151)
              ·
                refine ⟨68510465143145913846129227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45673643428763942564086151 68510465143145913846129227)
                ·
                  refine ⟨102765697714718870769193841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68510465143145913846129227 102765697714718870769193841)
                  ·
                    refine ⟨77074273286039153076895381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102765697714718870769193841 77074273286039153076895381)
                    ·
                      refine ⟨3612856560283085300479471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77074273286039153076895381 3612856560283085300479471)
                      ·
                        rfl

theorem cell23_7036013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7036013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036013 prefixEnd_7036013 := by exact prefixLift 7036013
  have htrace : WordTrace (prefixWord ++ tailWord_7036013) baseStart_7036013 baseEnd_7036013 := by
    simpa [prefixWord, tailWord_7036013, baseEnd_7036013] using wordTrace_append hprefix tailTrace_7036013
  have hstable : (prefixWord ++ tailWord_7036013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036013).length < 2 ^ (prefixWord ++ tailWord_7036013).sum := by decide
  have hdescent : baseEnd_7036013 < baseStart_7036013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036043 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4]
def baseStart_7036043 : Nat := 118140960795 + 7036043 * 2 ^ 59
def prefixEnd_7036043 : Nat := 4983230072969 + 3 ^ 40 * 7036043 * 2
def baseEnd_7036043 : Nat := 3612871964702720183104333

theorem tailTrace_7036043 : CollatzResearch.WordTrace tailWord_7036043 prefixEnd_7036043 3612871964702720183104333 := by
  unfold tailWord_7036043
  simp only [CollatzResearch.WordTrace]
  refine ⟨256625570848625346320432783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171083713899083564213621855 256625570848625346320432783)
  ·
    refine ⟨384938356272938019480649175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256625570848625346320432783 384938356272938019480649175)
    ·
      refine ⟨577407534409407029220973763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384938356272938019480649175 577407534409407029220973763)
      ·
        refine ⟨866111301614110543831460645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577407534409407029220973763 866111301614110543831460645)
        ·
          refine ⟨162395869052645726968398871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 866111301614110543831460645 162395869052645726968398871)
          ·
            refine ⟨243593803578968590452598307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162395869052645726968398871 243593803578968590452598307)
            ·
              refine ⟨365390705368452885678897461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243593803578968590452598307 365390705368452885678897461)
              ·
                refine ⟨34255378628292458032396637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365390705368452885678897461 34255378628292458032396637)
                ·
                  refine ⟨12845766985609671762148739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34255378628292458032396637 12845766985609671762148739)
                  ·
                    refine ⟨19268650478414507643223109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12845766985609671762148739 19268650478414507643223109)
                    ·
                      refine ⟨3612871964702720183104333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19268650478414507643223109 3612871964702720183104333)
                      ·
                        rfl

theorem cell23_7036043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4].length) (baseStart_7036043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036043 prefixEnd_7036043 := by exact prefixLift 7036043
  have htrace : WordTrace (prefixWord ++ tailWord_7036043) baseStart_7036043 baseEnd_7036043 := by
    simpa [prefixWord, tailWord_7036043, baseEnd_7036043] using wordTrace_append hprefix tailTrace_7036043
  have hstable : (prefixWord ++ tailWord_7036043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036043).length < 2 ^ (prefixWord ++ tailWord_7036043).sum := by decide
  have hdescent : baseEnd_7036043 < baseStart_7036043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036094 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_7036094 : Nat := 118140960795 + 7036094 * 2 ^ 59
def prefixEnd_7036094 : Nat := 4983230072969 + 3 ^ 40 * 7036094 * 2
def baseEnd_7036094 : Nat := 3612898152216099483566599

theorem tailTrace_7036094 : CollatzResearch.WordTrace tailWord_7036094 prefixEnd_7036094 3612898152216099483566599 := by
  unfold tailWord_7036094
  simp only [CollatzResearch.WordTrace]
  refine ⟨32078428871430072753817417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171084953980960388020359557 32078428871430072753817417)
  ·
    refine ⟨24058821653572554565363063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32078428871430072753817417 24058821653572554565363063)
    ·
      refine ⟨36088232480358831848044595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24058821653572554565363063 36088232480358831848044595)
      ·
        refine ⟨54132348720538247772066893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36088232480358831848044595 54132348720538247772066893)
        ·
          refine ⟨20299630770201842914525085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54132348720538247772066893 20299630770201842914525085)
          ·
            refine ⟨7612361538825691092946907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20299630770201842914525085 7612361538825691092946907)
            ·
              refine ⟨11418542308238536639420361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7612361538825691092946907 11418542308238536639420361)
              ·
                refine ⟨8563906731178902479565271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11418542308238536639420361 8563906731178902479565271)
                ·
                  refine ⟨12845860096768353719347907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8563906731178902479565271 12845860096768353719347907)
                  ·
                    refine ⟨19268790145152530579021861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12845860096768353719347907 19268790145152530579021861)
                    ·
                      refine ⟨3612898152216099483566599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19268790145152530579021861 3612898152216099483566599)
                      ·
                        rfl

theorem cell23_7036094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_7036094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036094 prefixEnd_7036094 := by exact prefixLift 7036094
  have htrace : WordTrace (prefixWord ++ tailWord_7036094) baseStart_7036094 baseEnd_7036094 := by
    simpa [prefixWord, tailWord_7036094, baseEnd_7036094] using wordTrace_append hprefix tailTrace_7036094
  have hstable : (prefixWord ++ tailWord_7036094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036094).length < 2 ^ (prefixWord ++ tailWord_7036094).sum := by decide
  have hdescent : baseEnd_7036094 < baseStart_7036094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036098 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7036098 : Nat := 118140960795 + 7036098 * 2 ^ 59
def prefixEnd_7036098 : Nat := 4983230072969 + 3 ^ 40 * 7036098 * 2
def baseEnd_7036098 : Nat := 3612900206138717467916581

theorem tailTrace_7036098 : CollatzResearch.WordTrace tailWord_7036098 prefixEnd_7036098 3612900206138717467916581 := by
  unfold tailWord_7036098
  simp only [CollatzResearch.WordTrace]
  refine ⟨64156894215856522678421237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171085051242284060475789965 64156894215856522678421237)
  ·
    refine ⟨6014708832736549001101991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64156894215856522678421237 6014708832736549001101991)
    ·
      refine ⟨9022063249104823501652987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014708832736549001101991 9022063249104823501652987)
      ·
        refine ⟨13533094873657235252479481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9022063249104823501652987 13533094873657235252479481)
        ·
          refine ⟨10149821155242926439359611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13533094873657235252479481 10149821155242926439359611)
          ·
            refine ⟨15224731732864389659039417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10149821155242926439359611 15224731732864389659039417)
            ·
              refine ⟨11418548799648292244279563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15224731732864389659039417 11418548799648292244279563)
              ·
                refine ⟨17127823199472438366419345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11418548799648292244279563 17127823199472438366419345)
                ·
                  refine ⟨12845867399604328774814509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17127823199472438366419345 12845867399604328774814509)
                  ·
                    refine ⟨4817200274851623290555441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12845867399604328774814509 4817200274851623290555441)
                    ·
                      refine ⟨3612900206138717467916581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817200274851623290555441 3612900206138717467916581)
                      ·
                        rfl

theorem cell23_7036098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7036098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036098 prefixEnd_7036098 := by exact prefixLift 7036098
  have htrace : WordTrace (prefixWord ++ tailWord_7036098) baseStart_7036098 baseEnd_7036098 := by
    simpa [prefixWord, tailWord_7036098, baseEnd_7036098] using wordTrace_append hprefix tailTrace_7036098
  have hstable : (prefixWord ++ tailWord_7036098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036098).length < 2 ^ (prefixWord ++ tailWord_7036098).sum := by decide
  have hdescent : baseEnd_7036098 < baseStart_7036098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036114 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7036114 : Nat := 118140960795 + 7036114 * 2 ^ 59
def prefixEnd_7036114 : Nat := 4983230072969 + 3 ^ 40 * 7036114 * 2
def baseEnd_7036114 : Nat := 3612908421829189405316507

theorem tailTrace_7036114 : CollatzResearch.WordTrace tailWord_7036114 prefixEnd_7036114 3612908421829189405316507 := by
  unfold tailWord_7036114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64157040107842031361566849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171085440287578750297511597 64157040107842031361566849)
  ·
    refine ⟨48117780080881523521175137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64157040107842031361566849 48117780080881523521175137)
    ·
      refine ⟨36088335060661142640881353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48117780080881523521175137 36088335060661142640881353)
      ·
        refine ⟨27066251295495856980661015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36088335060661142640881353 27066251295495856980661015)
        ·
          refine ⟨40599376943243785470991523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27066251295495856980661015 40599376943243785470991523)
          ·
            refine ⟨60899065414865678206487285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40599376943243785470991523 60899065414865678206487285)
            ·
              refine ⟨5709287382643657331858183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60899065414865678206487285 5709287382643657331858183)
              ·
                refine ⟨8563931073965485997787275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709287382643657331858183 8563931073965485997787275)
                ·
                  refine ⟨12845896610948228996680913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8563931073965485997787275 12845896610948228996680913)
                  ·
                    refine ⟨9634422458211171747510685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12845896610948228996680913 9634422458211171747510685)
                    ·
                      refine ⟨3612908421829189405316507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634422458211171747510685 3612908421829189405316507)
                      ·
                        rfl

theorem cell23_7036114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7036114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036114 prefixEnd_7036114 := by exact prefixLift 7036114
  have htrace : WordTrace (prefixWord ++ tailWord_7036114) baseStart_7036114 baseEnd_7036114 := by
    simpa [prefixWord, tailWord_7036114, baseEnd_7036114] using wordTrace_append hprefix tailTrace_7036114
  have hstable : (prefixWord ++ tailWord_7036114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036114).length < 2 ^ (prefixWord ++ tailWord_7036114).sum := by decide
  have hdescent : baseEnd_7036114 < baseStart_7036114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036127 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 3]
def baseStart_7036127 : Nat := 118140960795 + 7036127 * 2 ^ 59
def prefixEnd_7036127 : Nat := 4983230072969 + 3 ^ 40 * 7036127 * 2
def baseEnd_7036127 : Nat := 3612915097077697854453947

theorem tailTrace_7036127 : CollatzResearch.WordTrace tailWord_7036127 prefixEnd_7036127 3612915097077697854453947 := by
  unfold tailWord_7036127
  simp only [CollatzResearch.WordTrace]
  refine ⟨256628634580321028666490635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171085756386880685777660423 256628634580321028666490635)
  ·
    refine ⟨384942951870481542999735953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256628634580321028666490635 384942951870481542999735953)
    ·
      refine ⟨288707213902861157249801965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384942951870481542999735953 288707213902861157249801965)
      ·
        refine ⟨108265205213572933968675737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288707213902861157249801965 108265205213572933968675737)
        ·
          refine ⟨81198903910179700476506803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108265205213572933968675737 81198903910179700476506803)
          ·
            refine ⟨121798355865269550714760205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81198903910179700476506803 121798355865269550714760205)
            ·
              refine ⟨45674383449476081518035077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121798355865269550714760205 45674383449476081518035077)
              ·
                refine ⟨8563946896776765284631577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45674383449476081518035077 8563946896776765284631577)
                ·
                  refine ⟨6422960172582573963473683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8563946896776765284631577 6422960172582573963473683)
                  ·
                    refine ⟨9634440258873860945210525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422960172582573963473683 9634440258873860945210525)
                    ·
                      refine ⟨3612915097077697854453947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634440258873860945210525 3612915097077697854453947)
                      ·
                        rfl

theorem cell23_7036127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_7036127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036127 prefixEnd_7036127 := by exact prefixLift 7036127
  have htrace : WordTrace (prefixWord ++ tailWord_7036127) baseStart_7036127 baseEnd_7036127 := by
    simpa [prefixWord, tailWord_7036127, baseEnd_7036127] using wordTrace_append hprefix tailTrace_7036127
  have hstable : (prefixWord ++ tailWord_7036127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036127).length < 2 ^ (prefixWord ++ tailWord_7036127).sum := by decide
  have hdescent : baseEnd_7036127 < baseStart_7036127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036128 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 1, 2, 2]
def baseStart_7036128 : Nat := 118140960795 + 7036128 * 2 ^ 59
def prefixEnd_7036128 : Nat := 4983230072969 + 3 ^ 40 * 7036128 * 2
def baseEnd_7036128 : Nat := 3612915610558352350541443

theorem tailTrace_7036128 : CollatzResearch.WordTrace tailWord_7036128 prefixEnd_7036128 3612915610558352350541443 := by
  unfold tailWord_7036128
  simp only [CollatzResearch.WordTrace]
  refine ⟨128314335526658702918638519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171085780702211603891518025 128314335526658702918638519)
  ·
    refine ⟨192471503289988054377957779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128314335526658702918638519 192471503289988054377957779)
    ·
      refine ⟨288707254934982081566936669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192471503289988054377957779 288707254934982081566936669)
      ·
        refine ⟨108265220600618280587601251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288707254934982081566936669 108265220600618280587601251)
        ·
          refine ⟨162397830900927420881401877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108265220600618280587601251 162397830900927420881401877)
          ·
            refine ⟨7612398323480972853815713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162397830900927420881401877 7612398323480972853815713)
            ·
              refine ⟨5709298742610729640361785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612398323480972853815713 5709298742610729640361785)
              ·
                refine ⟨4281974056958047230271339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709298742610729640361785 4281974056958047230271339)
                ·
                  refine ⟨6422961085437070845407009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281974056958047230271339 6422961085437070845407009)
                  ·
                    refine ⟨4817220814077803134055257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6422961085437070845407009 4817220814077803134055257)
                    ·
                      refine ⟨3612915610558352350541443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817220814077803134055257 3612915610558352350541443)
                      ·
                        rfl

theorem cell23_7036128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_7036128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036128 prefixEnd_7036128 := by exact prefixLift 7036128
  have htrace : WordTrace (prefixWord ++ tailWord_7036128) baseStart_7036128 baseEnd_7036128 := by
    simpa [prefixWord, tailWord_7036128, baseEnd_7036128] using wordTrace_append hprefix tailTrace_7036128
  have hstable : (prefixWord ++ tailWord_7036128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036128).length < 2 ^ (prefixWord ++ tailWord_7036128).sum := by decide
  have hdescent : baseEnd_7036128 < baseStart_7036128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036150 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7036150 : Nat := 118140960795 + 7036150 * 2 ^ 59
def prefixEnd_7036150 : Nat := 4983230072969 + 3 ^ 40 * 7036150 * 2
def baseEnd_7036150 : Nat := 3612926907132751264466341

theorem tailTrace_7036150 : CollatzResearch.WordTrace tailWord_7036150 prefixEnd_7036150 3612926907132751264466341 := by
  unfold tailWord_7036150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039342091202356474661119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171086315639491802396385269 16039342091202356474661119)
  ·
    refine ⟨24059013136803534711991679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16039342091202356474661119 24059013136803534711991679)
    ·
      refine ⟨36088519705205302067987519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24059013136803534711991679 36088519705205302067987519)
      ·
        refine ⟨54132779557807953101981279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36088519705205302067987519 54132779557807953101981279)
        ·
          refine ⟨81199169336711929652971919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54132779557807953101981279 81199169336711929652971919)
          ·
            refine ⟨121798754005067894479457879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81199169336711929652971919 121798754005067894479457879)
            ·
              refine ⟨182698131007601841719186819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121798754005067894479457879 182698131007601841719186819)
              ·
                refine ⟨274047196511402762578780229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182698131007601841719186819 274047196511402762578780229)
                ·
                  refine ⟨51383849345888017983521293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274047196511402762578780229 51383849345888017983521293)
                  ·
                    refine ⟨19268943504708006743820485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51383849345888017983521293 19268943504708006743820485)
                    ·
                      refine ⟨3612926907132751264466341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19268943504708006743820485 3612926907132751264466341)
                      ·
                        rfl

theorem cell23_7036150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7036150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036150 prefixEnd_7036150 := by exact prefixLift 7036150
  have htrace : WordTrace (prefixWord ++ tailWord_7036150) baseStart_7036150 baseEnd_7036150 := by
    simpa [prefixWord, tailWord_7036150, baseEnd_7036150] using wordTrace_append hprefix tailTrace_7036150
  have hstable : (prefixWord ++ tailWord_7036150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036150).length < 2 ^ (prefixWord ++ tailWord_7036150).sum := by decide
  have hdescent : baseEnd_7036150 < baseStart_7036150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036171 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 1, 3, 2]
def baseStart_7036171 : Nat := 118140960795 + 7036171 * 2 ^ 59
def prefixEnd_7036171 : Nat := 4983230072969 + 3 ^ 40 * 7036171 * 2
def baseEnd_7036171 : Nat := 3612937690226495682303745

theorem tailTrace_7036171 : CollatzResearch.WordTrace tailWord_7036171 prefixEnd_7036171 3612937690226495682303745 := by
  unfold tailWord_7036171
  simp only [CollatzResearch.WordTrace]
  refine ⟨256630239392161624181092367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171086826261441082787394911 256630239392161624181092367)
  ·
    refine ⟨384945359088242436271638551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256630239392161624181092367 384945359088242436271638551)
    ·
      refine ⟨577418038632363654407457827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384945359088242436271638551 577418038632363654407457827)
      ·
        refine ⟨866127057948545481611186741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577418038632363654407457827 866127057948545481611186741)
        ·
          refine ⟨81199411682676138901048757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 866127057948545481611186741 81199411682676138901048757)
          ·
            refine ⟨7612444845250888021973321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81199411682676138901048757 7612444845250888021973321)
            ·
              refine ⟨5709333633938166016479991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612444845250888021973321 5709333633938166016479991)
              ·
                refine ⟨8564000450907249024719987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709333633938166016479991 8564000450907249024719987)
                ·
                  refine ⟨12846000676360873537079981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564000450907249024719987 12846000676360873537079981)
                  ·
                    refine ⟨4817250253635327576404993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12846000676360873537079981 4817250253635327576404993)
                    ·
                      refine ⟨3612937690226495682303745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817250253635327576404993 3612937690226495682303745)
                      ·
                        rfl

theorem cell23_7036171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 3, 2].length) (baseStart_7036171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036171 prefixEnd_7036171 := by exact prefixLift 7036171
  have htrace : WordTrace (prefixWord ++ tailWord_7036171) baseStart_7036171 baseEnd_7036171 := by
    simpa [prefixWord, tailWord_7036171, baseEnd_7036171] using wordTrace_append hprefix tailTrace_7036171
  have hstable : (prefixWord ++ tailWord_7036171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036171).length < 2 ^ (prefixWord ++ tailWord_7036171).sum := by decide
  have hdescent : baseEnd_7036171 < baseStart_7036171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036184 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7036184 : Nat := 118140960795 + 7036184 * 2 ^ 59
def prefixEnd_7036184 : Nat := 4983230072969 + 3 ^ 40 * 7036184 * 2
def baseEnd_7036184 : Nat := 3612944365475004131441185

theorem tailTrace_7036184 : CollatzResearch.WordTrace tailWord_7036184 prefixEnd_7036184 3612944365475004131441185 := by
  unfold tailWord_7036184
  simp only [CollatzResearch.WordTrace]
  refine ⟨128315356770557263700657803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171087142360743018267543737 128315356770557263700657803)
  ·
    refine ⟨192473035155835895550986705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128315356770557263700657803 192473035155835895550986705)
    ·
      refine ⟨144354776366876921663240029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192473035155835895550986705 144354776366876921663240029)
      ·
        refine ⟨54133041137578845623715011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144354776366876921663240029 54133041137578845623715011)
        ·
          refine ⟨81199561706368268435572517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54133041137578845623715011 81199561706368268435572517)
          ·
            refine ⟨15224917819944050331669847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81199561706368268435572517 15224917819944050331669847)
            ·
              refine ⟨22837376729916075497504771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15224917819944050331669847 22837376729916075497504771)
              ·
                refine ⟨34256065094874113246257157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22837376729916075497504771 34256065094874113246257157)
                ·
                  refine ⟨6423012205288896233673217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34256065094874113246257157 6423012205288896233673217)
                  ·
                    refine ⟨4817259153966672175254913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6423012205288896233673217 4817259153966672175254913)
                    ·
                      refine ⟨3612944365475004131441185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817259153966672175254913 3612944365475004131441185)
                      ·
                        rfl

theorem cell23_7036184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7036184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036184 prefixEnd_7036184 := by exact prefixLift 7036184
  have htrace : WordTrace (prefixWord ++ tailWord_7036184) baseStart_7036184 baseEnd_7036184 := by
    simpa [prefixWord, tailWord_7036184, baseEnd_7036184] using wordTrace_append hprefix tailTrace_7036184
  have hstable : (prefixWord ++ tailWord_7036184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036184).length < 2 ^ (prefixWord ++ tailWord_7036184).sum := by decide
  have hdescent : baseEnd_7036184 < baseStart_7036184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036220 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_7036220 : Nat := 118140960795 + 7036220 * 2 ^ 59
def prefixEnd_7036220 : Nat := 4983230072969 + 3 ^ 40 * 7036220 * 2
def baseEnd_7036220 : Nat := 1204320950259521996863673

theorem tailTrace_7036220 : CollatzResearch.WordTrace tailWord_7036220 prefixEnd_7036220 1204320950259521996863673 := by
  unfold tailWord_7036220
  simp only [CollatzResearch.WordTrace]
  refine ⟨128316013284492052774813057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171088017712656070366417409 128316013284492052774813057)
  ·
    refine ⟨96237009963369039581109793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128316013284492052774813057 96237009963369039581109793)
    ·
      refine ⟨72177757472526779685832345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96237009963369039581109793 72177757472526779685832345)
      ·
        refine ⟨54133318104395084764374259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72177757472526779685832345 54133318104395084764374259)
        ·
          refine ⟨81199977156592627146561389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54133318104395084764374259 81199977156592627146561389)
          ·
            refine ⟨30449991433722235179960521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81199977156592627146561389 30449991433722235179960521)
            ·
              refine ⟨22837493575291676384970391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30449991433722235179960521 22837493575291676384970391)
              ·
                refine ⟨34256240362937514577455587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22837493575291676384970391 34256240362937514577455587)
                ·
                  refine ⟨51384360544406271866183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34256240362937514577455587 51384360544406271866183381)
                  ·
                    refine ⟨1204320950259521996863673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51384360544406271866183381 1204320950259521996863673)
                    ·
                      rfl

theorem cell23_7036220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_7036220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036220 prefixEnd_7036220 := by exact prefixLift 7036220
  have htrace : WordTrace (prefixWord ++ tailWord_7036220) baseStart_7036220 baseEnd_7036220 := by
    simpa [prefixWord, tailWord_7036220, baseEnd_7036220] using wordTrace_append hprefix tailTrace_7036220
  have hstable : (prefixWord ++ tailWord_7036220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036220).length < 2 ^ (prefixWord ++ tailWord_7036220).sum := by decide
  have hdescent : baseEnd_7036220 < baseStart_7036220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036257 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_7036257 : Nat := 118140960795 + 7036257 * 2 ^ 59
def prefixEnd_7036257 : Nat := 4983230072969 + 3 ^ 40 * 7036257 * 2
def baseEnd_7036257 : Nat := 3612981849562782345828349

theorem tailTrace_7036257 : CollatzResearch.WordTrace tailWord_7036257 prefixEnd_7036257 3612981849562782345828349 := by
  unfold tailWord_7036257
  simp only [CollatzResearch.WordTrace]
  refine ⟨256633376069850060868723025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171088917379900040579148683 256633376069850060868723025)
  ·
    refine ⟨192475032052387545651542269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256633376069850060868723025 192475032052387545651542269)
    ·
      refine ⟨72178137019645329619328351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192475032052387545651542269 72178137019645329619328351)
      ·
        refine ⟨108267205529467994428992527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72178137019645329619328351 108267205529467994428992527)
        ·
          refine ⟨162400808294201991643488791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108267205529467994428992527 162400808294201991643488791)
          ·
            refine ⟨243601212441302987465233187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162400808294201991643488791 243601212441302987465233187)
            ·
              refine ⟨365401818661954481197849781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243601212441302987465233187 365401818661954481197849781)
              ·
                refine ⟨34256420499558232612298417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365401818661954481197849781 34256420499558232612298417)
                ·
                  refine ⟨25692315374668674459223813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34256420499558232612298417 25692315374668674459223813)
                  ·
                    refine ⟨4817309132750376461104465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25692315374668674459223813 4817309132750376461104465)
                    ·
                      refine ⟨3612981849562782345828349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817309132750376461104465 3612981849562782345828349)
                      ·
                        rfl

theorem cell23_7036257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_7036257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036257 prefixEnd_7036257 := by exact prefixLift 7036257
  have htrace : WordTrace (prefixWord ++ tailWord_7036257) baseStart_7036257 baseEnd_7036257 := by
    simpa [prefixWord, tailWord_7036257, baseEnd_7036257] using wordTrace_append hprefix tailTrace_7036257
  have hstable : (prefixWord ++ tailWord_7036257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036257).length < 2 ^ (prefixWord ++ tailWord_7036257).sum := by decide
  have hdescent : baseEnd_7036257 < baseStart_7036257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036284 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_7036284 : Nat := 118140960795 + 7036284 * 2 ^ 59
def prefixEnd_7036284 : Nat := 4983230072969 + 3 ^ 40 * 7036284 * 2
def baseEnd_7036284 : Nat := 1204331904513484580063575

theorem tailTrace_7036284 : CollatzResearch.WordTrace tailWord_7036284 prefixEnd_7036284 1204331904513484580063575 := by
  unfold tailWord_7036284
  simp only [CollatzResearch.WordTrace]
  refine ⟨128317180420376122239977953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171089573893834829653303937 128317180420376122239977953)
  ·
    refine ⟨96237885315282091679983465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128317180420376122239977953 96237885315282091679983465)
    ·
      refine ⟨72178413986461568759987599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96237885315282091679983465 72178413986461568759987599)
      ·
        refine ⟨108267620979692353139981399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72178413986461568759987599 108267620979692353139981399)
        ·
          refine ⟨162401431469538529709972099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108267620979692353139981399 162401431469538529709972099)
          ·
            refine ⟨243602147204307794564958149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162401431469538529709972099 243602147204307794564958149)
            ·
              refine ⟨45675402600807711480929653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243602147204307794564958149 45675402600807711480929653)
              ·
                refine ⟨4282068993825722951337155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45675402600807711480929653 4282068993825722951337155)
                ·
                  refine ⟨6423103490738584427005733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282068993825722951337155 6423103490738584427005733)
                  ·
                    refine ⟨1204331904513484580063575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423103490738584427005733 1204331904513484580063575)
                    ·
                      rfl

theorem cell23_7036284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_7036284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036284 prefixEnd_7036284 := by exact prefixLift 7036284
  have htrace : WordTrace (prefixWord ++ tailWord_7036284) baseStart_7036284 baseEnd_7036284 := by
    simpa [prefixWord, tailWord_7036284, baseEnd_7036284] using wordTrace_append hprefix tailTrace_7036284
  have hstable : (prefixWord ++ tailWord_7036284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036284).length < 2 ^ (prefixWord ++ tailWord_7036284).sum := by decide
  have hdescent : baseEnd_7036284 < baseStart_7036284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036300 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7036300 : Nat := 118140960795 + 7036300 * 2 ^ 59
def prefixEnd_7036300 : Nat := 4983230072969 + 3 ^ 40 * 7036300 * 2
def baseEnd_7036300 : Nat := 3613003929230925677590651

theorem tailTrace_7036300 : CollatzResearch.WordTrace tailWord_7036300 prefixEnd_7036300 3613003929230925677590651 := by
  unfold tailWord_7036300
  simp only [CollatzResearch.WordTrace]
  refine ⟨128317472204347139606269177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171089962939129519475025569 128317472204347139606269177)
  ·
    refine ⟨96238104153260354704701883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128317472204347139606269177 96238104153260354704701883)
    ·
      refine ⟨144357156229890532057052825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96238104153260354704701883 144357156229890532057052825)
      ·
        refine ⟨108267867172417899042789619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144357156229890532057052825 108267867172417899042789619)
        ·
          refine ⟨162401800758626848564184429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108267867172417899042789619 162401800758626848564184429)
          ·
            refine ⟨60900675284485068211569161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162401800758626848564184429 60900675284485068211569161)
            ·
              refine ⟨45675506463363801158676871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60900675284485068211569161 45675506463363801158676871)
              ·
                refine ⟨68513259695045701738015307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45675506463363801158676871 68513259695045701738015307)
                ·
                  refine ⟨102769889542568552607022961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68513259695045701738015307 102769889542568552607022961)
                  ·
                    refine ⟨77077417156926414455267221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102769889542568552607022961 77077417156926414455267221)
                    ·
                      refine ⟨3613003929230925677590651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77077417156926414455267221 3613003929230925677590651)
                      ·
                        rfl

theorem cell23_7036300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7036300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036300 prefixEnd_7036300 := by exact prefixLift 7036300
  have htrace : WordTrace (prefixWord ++ tailWord_7036300) baseStart_7036300 baseEnd_7036300 := by
    simpa [prefixWord, tailWord_7036300, baseEnd_7036300] using wordTrace_append hprefix tailTrace_7036300
  have hstable : (prefixWord ++ tailWord_7036300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036300).length < 2 ^ (prefixWord ++ tailWord_7036300).sum := by decide
  have hdescent : baseEnd_7036300 < baseStart_7036300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036307 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 3]
def baseStart_7036307 : Nat := 118140960795 + 7036307 * 2 ^ 59
def prefixEnd_7036307 : Nat := 4983230072969 + 3 ^ 40 * 7036307 * 2
def baseEnd_7036307 : Nat := 3613007523595507150203119

theorem tailTrace_7036307 : CollatzResearch.WordTrace tailWord_7036307 prefixEnd_7036307 3613007523595507150203119 := by
  unfold tailWord_7036307
  simp only [CollatzResearch.WordTrace]
  refine ⟨256635199719668919408043175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171090133146445946272028783 256635199719668919408043175)
  ·
    refine ⟨384952799579503379112064763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256635199719668919408043175 384952799579503379112064763)
    ·
      refine ⟨577429199369255068668097145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384952799579503379112064763 577429199369255068668097145)
      ·
        refine ⟨433071899526941301501072859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577429199369255068668097145 433071899526941301501072859)
        ·
          refine ⟨649607849290411952251609289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433071899526941301501072859 649607849290411952251609289)
          ·
            refine ⟨487205886967808964188706967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649607849290411952251609289 487205886967808964188706967)
            ·
              refine ⟨730808830451713446283060451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487205886967808964188706967 730808830451713446283060451)
              ·
                refine ⟨1096213245677570169424590677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730808830451713446283060451 1096213245677570169424590677)
                ·
                  refine ⟨6423124486392012711472211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1096213245677570169424590677 6423124486392012711472211)
                  ·
                    refine ⟨9634686729588019067208317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6423124486392012711472211 9634686729588019067208317)
                    ·
                      refine ⟨3613007523595507150203119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634686729588019067208317 3613007523595507150203119)
                      ·
                        rfl

theorem cell23_7036307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_7036307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036307 prefixEnd_7036307 := by exact prefixLift 7036307
  have htrace : WordTrace (prefixWord ++ tailWord_7036307) baseStart_7036307 baseEnd_7036307 := by
    simpa [prefixWord, tailWord_7036307, baseEnd_7036307] using wordTrace_append hprefix tailTrace_7036307
  have hstable : (prefixWord ++ tailWord_7036307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036307).length < 2 ^ (prefixWord ++ tailWord_7036307).sum := by decide
  have hdescent : baseEnd_7036307 < baseStart_7036307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036320 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_7036320 : Nat := 118140960795 + 7036320 * 2 ^ 59
def prefixEnd_7036320 : Nat := 4983230072969 + 3 ^ 40 * 7036320 * 2
def baseEnd_7036320 : Nat := 3613014198844015599340559

theorem tailTrace_7036320 : CollatzResearch.WordTrace tailWord_7036320 prefixEnd_7036320 3613014198844015599340559 := by
  unfold tailWord_7036320
  simp only [CollatzResearch.WordTrace]
  refine ⟨128317836934310911314133207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171090449245747881752177609 128317836934310911314133207)
  ·
    refine ⟨192476755401466366971199811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128317836934310911314133207 192476755401466366971199811)
    ·
      refine ⟨288715133102199550456799717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192476755401466366971199811 288715133102199550456799717)
      ·
        refine ⟨54134087456662415710649947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288715133102199550456799717 54134087456662415710649947)
        ·
          refine ⟨81201131184993623565974921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54134087456662415710649947 81201131184993623565974921)
          ·
            refine ⟨60900848388745217674481191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81201131184993623565974921 60900848388745217674481191)
            ·
              refine ⟨91351272583117826511721787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60900848388745217674481191 91351272583117826511721787)
              ·
                refine ⟨137026908874676739767582681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91351272583117826511721787 137026908874676739767582681)
                ·
                  refine ⟨102770181656007554825687011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137026908874676739767582681 102770181656007554825687011)
                  ·
                    refine ⟨154155272484011332238530517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102770181656007554825687011 154155272484011332238530517)
                    ·
                      refine ⟨3613014198844015599340559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154155272484011332238530517 3613014198844015599340559)
                      ·
                        rfl

theorem cell23_7036320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_7036320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036320 prefixEnd_7036320 := by exact prefixLift 7036320
  have htrace : WordTrace (prefixWord ++ tailWord_7036320) baseStart_7036320 baseEnd_7036320 := by
    simpa [prefixWord, tailWord_7036320, baseEnd_7036320] using wordTrace_append hprefix tailTrace_7036320
  have hstable : (prefixWord ++ tailWord_7036320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036320).length < 2 ^ (prefixWord ++ tailWord_7036320).sum := by decide
  have hdescent : baseEnd_7036320 < baseStart_7036320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036327 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 3, 5]
def baseStart_7036327 : Nat := 118140960795 + 7036327 * 2 ^ 59
def prefixEnd_7036327 : Nat := 4983230072969 + 3 ^ 40 * 7036327 * 2
def baseEnd_7036327 : Nat := 1204339264402865690651009

theorem tailTrace_7036327 : CollatzResearch.WordTrace tailWord_7036327 prefixEnd_7036327 1204339264402865690651009 := by
  unfold tailWord_7036327
  simp only [CollatzResearch.WordTrace]
  refine ⟨256635929179596462823771235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171090619453064308549180823 256635929179596462823771235)
  ·
    refine ⟨384953893769394694235656853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256635929179596462823771235 384953893769394694235656853)
    ·
      refine ⟨18044713770440376292296415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 384953893769394694235656853 18044713770440376292296415)
      ·
        refine ⟨27067070655660564438444623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18044713770440376292296415 27067070655660564438444623)
        ·
          refine ⟨40600605983490846657666935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27067070655660564438444623 40600605983490846657666935)
          ·
            refine ⟨60900908975236269986500403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40600605983490846657666935 60900908975236269986500403)
            ·
              refine ⟨91351363462854404979750605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60900908975236269986500403 91351363462854404979750605)
              ·
                refine ⟨34256761298570401867406477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91351363462854404979750605 34256761298570401867406477)
                ·
                  refine ⟨12846285486963900700277429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34256761298570401867406477 12846285486963900700277429)
                  ·
                    refine ⟨1204339264402865690651009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12846285486963900700277429 1204339264402865690651009)
                    ·
                      rfl

theorem cell23_7036327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_7036327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036327 prefixEnd_7036327 := by exact prefixLift 7036327
  have htrace : WordTrace (prefixWord ++ tailWord_7036327) baseStart_7036327 baseEnd_7036327 := by
    simpa [prefixWord, tailWord_7036327, baseEnd_7036327] using wordTrace_append hprefix tailTrace_7036327
  have hstable : (prefixWord ++ tailWord_7036327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036327).length < 2 ^ (prefixWord ++ tailWord_7036327).sum := by decide
  have hdescent : baseEnd_7036327 < baseStart_7036327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036328 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7036328 : Nat := 118140960795 + 7036328 * 2 ^ 59
def prefixEnd_7036328 : Nat := 4983230072969 + 3 ^ 40 * 7036328 * 2
def baseEnd_7036328 : Nat := 3613018306689251568040523

theorem tailTrace_7036328 : CollatzResearch.WordTrace tailWord_7036328 prefixEnd_7036328 3613018306689251568040523 := by
  unfold tailWord_7036328
  simp only [CollatzResearch.WordTrace]
  refine ⟨128317982826296419997278819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171090643768395226663038425 128317982826296419997278819)
  ·
    refine ⟨192476974239444629995918229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128317982826296419997278819 192476974239444629995918229)
    ·
      refine ⟨9022358167473967031058667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192476974239444629995918229 9022358167473967031058667)
      ·
        refine ⟨13533537251210950546588001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9022358167473967031058667 13533537251210950546588001)
        ·
          refine ⟨10150152938408212909941001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13533537251210950546588001 10150152938408212909941001)
          ·
            refine ⟨7612614703806159682455751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10150152938408212909941001 7612614703806159682455751)
            ·
              refine ⟨11418922055709239523683627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7612614703806159682455751 11418922055709239523683627)
              ·
                refine ⟨17128383083563859285525441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11418922055709239523683627 17128383083563859285525441)
                ·
                  refine ⟨12846287312672894464144081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17128383083563859285525441 12846287312672894464144081)
                  ·
                    refine ⟨9634715484504670848108061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12846287312672894464144081 9634715484504670848108061)
                    ·
                      refine ⟨3613018306689251568040523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634715484504670848108061 3613018306689251568040523)
                      ·
                        rfl

theorem cell23_7036328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7036328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036328 prefixEnd_7036328 := by exact prefixLift 7036328
  have htrace : WordTrace (prefixWord ++ tailWord_7036328) baseStart_7036328 baseEnd_7036328 := by
    simpa [prefixWord, tailWord_7036328, baseEnd_7036328] using wordTrace_append hprefix tailTrace_7036328
  have hstable : (prefixWord ++ tailWord_7036328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036328).length < 2 ^ (prefixWord ++ tailWord_7036328).sum := by decide
  have hdescent : baseEnd_7036328 < baseStart_7036328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036344 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 1, 5]
def baseStart_7036344 : Nat := 118140960795 + 7036344 * 2 ^ 59
def prefixEnd_7036344 : Nat := 4983230072969 + 3 ^ 40 * 7036344 * 2
def baseEnd_7036344 : Nat := 1204342174126574501813483

theorem tailTrace_7036344 : CollatzResearch.WordTrace tailWord_7036344 prefixEnd_7036344 1204342174126574501813483 := by
  unfold tailWord_7036344
  simp only [CollatzResearch.WordTrace]
  refine ⟨128318274610267437363570043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171091032813689916484760057 128318274610267437363570043)
  ·
    refine ⟨192477411915401156045355065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128318274610267437363570043 192477411915401156045355065)
    ·
      refine ⟨144358058936550867034016299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192477411915401156045355065 144358058936550867034016299)
      ·
        refine ⟨216537088404826300551024449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144358058936550867034016299 216537088404826300551024449)
        ·
          refine ⟨162402816303619725413268337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216537088404826300551024449 162402816303619725413268337)
          ·
            refine ⟨121802112227714794059951253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162402816303619725413268337 121802112227714794059951253)
            ·
              refine ⟨5709474010674130971560215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121802112227714794059951253 5709474010674130971560215)
              ·
                refine ⟨8564211016011196457340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709474010674130971560215 8564211016011196457340323)
                ·
                  refine ⟨12846316524016794686010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564211016011196457340323 12846316524016794686010485)
                  ·
                    refine ⟨1204342174126574501813483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12846316524016794686010485 1204342174126574501813483)
                    ·
                      rfl

theorem cell23_7036344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_7036344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036344 prefixEnd_7036344 := by exact prefixLift 7036344
  have htrace : WordTrace (prefixWord ++ tailWord_7036344) baseStart_7036344 baseEnd_7036344 := by
    simpa [prefixWord, tailWord_7036344, baseEnd_7036344] using wordTrace_append hprefix tailTrace_7036344
  have hstable : (prefixWord ++ tailWord_7036344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036344).length < 2 ^ (prefixWord ++ tailWord_7036344).sum := by decide
  have hdescent : baseEnd_7036344 < baseStart_7036344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036367 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_7036367 : Nat := 118140960795 + 7036367 * 2 ^ 59
def prefixEnd_7036367 : Nat := 4983230072969 + 3 ^ 40 * 7036367 * 2
def baseEnd_7036367 : Nat := 3613038332434776915452843

theorem tailTrace_7036367 : CollatzResearch.WordTrace tailWord_7036367 prefixEnd_7036367 3613038332434776915452843 := by
  unfold tailWord_7036367
  simp only [CollatzResearch.WordTrace]
  refine ⟨256637388099451549655227355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171091592066301033103484903 256637388099451549655227355)
  ·
    refine ⟨384956082149177324482841033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256637388099451549655227355 384956082149177324482841033)
    ·
      refine ⟨288717061611882993362130775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384956082149177324482841033 288717061611882993362130775)
      ·
        refine ⟨433075592417824490043196163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288717061611882993362130775 433075592417824490043196163)
        ·
          refine ⟨649613388626736735064794245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433075592417824490043196163 649613388626736735064794245)
          ·
            refine ⟨121802510367513137824648921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 649613388626736735064794245 121802510367513137824648921)
            ·
              refine ⟨91351882775634853368486691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121802510367513137824648921 91351882775634853368486691)
              ·
                refine ⟨137027824163452280052730037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91351882775634853368486691 137027824163452280052730037)
                ·
                  refine ⟨12846358515323651254943441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137027824163452280052730037 12846358515323651254943441)
                  ·
                    refine ⟨9634768886492738441207581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12846358515323651254943441 9634768886492738441207581)
                    ·
                      refine ⟨3613038332434776915452843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9634768886492738441207581 3613038332434776915452843)
                      ·
                        rfl

theorem cell23_7036367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_7036367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036367 prefixEnd_7036367 := by exact prefixLift 7036367
  have htrace : WordTrace (prefixWord ++ tailWord_7036367) baseStart_7036367 baseEnd_7036367 := by
    simpa [prefixWord, tailWord_7036367, baseEnd_7036367] using wordTrace_append hprefix tailTrace_7036367
  have hstable : (prefixWord ++ tailWord_7036367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036367).length < 2 ^ (prefixWord ++ tailWord_7036367).sum := by decide
  have hdescent : baseEnd_7036367 < baseStart_7036367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036377 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_7036377 : Nat := 118140960795 + 7036377 * 2 ^ 59
def prefixEnd_7036377 : Nat := 4983230072969 + 3 ^ 40 * 7036377 * 2
def baseEnd_7036377 : Nat := 3613043467241321876327797

theorem tailTrace_7036377 : CollatzResearch.WordTrace tailWord_7036377 prefixEnd_7036377 3613043467241321876327797 := by
  unfold tailWord_7036377
  simp only [CollatzResearch.WordTrace]
  refine ⟨256637752829415321363091385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171091835219610214242060923 256637752829415321363091385)
  ·
    refine ⟨192478314622061491022318539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256637752829415321363091385 192478314622061491022318539)
    ·
      refine ⟨288717471933092236533477809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192478314622061491022318539 288717471933092236533477809)
      ·
        refine ⟨216538103949819177400108357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288717471933092236533477809 216538103949819177400108357)
        ·
          refine ⟨40600894490591095762520317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216538103949819177400108357 40600894490591095762520317)
          ·
            refine ⟨15225335433971660910945119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40600894490591095762520317 15225335433971660910945119)
            ·
              refine ⟨22838003150957491366417679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15225335433971660910945119 22838003150957491366417679)
              ·
                refine ⟨34257004726436237049626519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22838003150957491366417679 34257004726436237049626519)
                ·
                  refine ⟨51385507089654355574439779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34257004726436237049626519 51385507089654355574439779)
                  ·
                    refine ⟨77078260634481533361659669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51385507089654355574439779 77078260634481533361659669)
                    ·
                      refine ⟨3613043467241321876327797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77078260634481533361659669 3613043467241321876327797)
                      ·
                        rfl

theorem cell23_7036377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_7036377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036377 prefixEnd_7036377 := by exact prefixLift 7036377
  have htrace : WordTrace (prefixWord ++ tailWord_7036377) baseStart_7036377 baseEnd_7036377 := by
    simpa [prefixWord, tailWord_7036377, baseEnd_7036377] using wordTrace_append hprefix tailTrace_7036377
  have hstable : (prefixWord ++ tailWord_7036377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036377).length < 2 ^ (prefixWord ++ tailWord_7036377).sum := by decide
  have hdescent : baseEnd_7036377 < baseStart_7036377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036381 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_7036381 : Nat := 118140960795 + 7036381 * 2 ^ 59
def prefixEnd_7036381 : Nat := 4983230072969 + 3 ^ 40 * 7036381 * 2
def baseEnd_7036381 : Nat := 3613045521163939860677779

theorem tailTrace_7036381 : CollatzResearch.WordTrace tailWord_7036381 prefixEnd_7036381 3613045521163939860677779 := by
  unfold tailWord_7036381
  simp only [CollatzResearch.WordTrace]
  refine ⟨256637898721400830046236997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171091932480933886697491331 256637898721400830046236997)
  ·
    refine ⟨48119606010262655633669437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256637898721400830046236997 48119606010262655633669437)
    ·
      refine ⟨18044852253848495862626039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48119606010262655633669437 18044852253848495862626039)
      ·
        refine ⟨27067278380772743793939059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18044852253848495862626039 27067278380772743793939059)
        ·
          refine ⟨40600917571159115690908589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27067278380772743793939059 40600917571159115690908589)
          ·
            refine ⟨15225344089184668384090721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40600917571159115690908589 15225344089184668384090721)
            ·
              refine ⟨11419008066888501288068041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15225344089184668384090721 11419008066888501288068041)
              ·
                refine ⟨8564256050166375966051031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11419008066888501288068041 8564256050166375966051031)
                ·
                  refine ⟨12846384075249563949076547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564256050166375966051031 12846384075249563949076547)
                  ·
                    refine ⟨19269576112874345923614821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12846384075249563949076547 19269576112874345923614821)
                    ·
                      refine ⟨3613045521163939860677779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19269576112874345923614821 3613045521163939860677779)
                      ·
                        rfl

theorem cell23_7036381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_7036381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036381 prefixEnd_7036381 := by exact prefixLift 7036381
  have htrace : WordTrace (prefixWord ++ tailWord_7036381) baseStart_7036381 baseEnd_7036381 := by
    simpa [prefixWord, tailWord_7036381, baseEnd_7036381] using wordTrace_append hprefix tailTrace_7036381
  have hstable : (prefixWord ++ tailWord_7036381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036381).length < 2 ^ (prefixWord ++ tailWord_7036381).sum := by decide
  have hdescent : baseEnd_7036381 < baseStart_7036381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036387 : List Nat := [1, 1, 1, 6, 2, 2, 1, 9]
def baseStart_7036387 : Nat := 118140960795 + 7036387 * 2 ^ 59
def prefixEnd_7036387 : Nat := 4983230072969 + 3 ^ 40 * 7036387 * 2
def baseEnd_7036387 : Nat := 133816614890661734711213

theorem tailTrace_7036387 : CollatzResearch.WordTrace tailWord_7036387 prefixEnd_7036387 133816614890661734711213 := by
  unfold tailWord_7036387
  simp only [CollatzResearch.WordTrace]
  refine ⟨256638117559379093070955415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171092078372919395380636943 256638117559379093070955415)
  ·
    refine ⟨384957176339068639606433123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256638117559379093070955415 384957176339068639606433123)
    ·
      refine ⟨577435764508602959409649685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384957176339068639606433123 577435764508602959409649685)
      ·
        refine ⟨27067301461340763722327329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 577435764508602959409649685 27067301461340763722327329)
        ·
          refine ⟨20300476096005572791745497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27067301461340763722327329 20300476096005572791745497)
          ·
            refine ⟨15225357072004179593809123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20300476096005572791745497 15225357072004179593809123)
            ·
              refine ⟨22838035608006269390713685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15225357072004179593809123 22838035608006269390713685)
              ·
                refine ⟨133816614890661734711213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22838035608006269390713685 133816614890661734711213)
                ·
                  rfl

theorem cell23_7036387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 9].length) (baseStart_7036387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036387 prefixEnd_7036387 := by exact prefixLift 7036387
  have htrace : WordTrace (prefixWord ++ tailWord_7036387) baseStart_7036387 baseEnd_7036387 := by
    simpa [prefixWord, tailWord_7036387, baseEnd_7036387] using wordTrace_append hprefix tailTrace_7036387
  have hstable : (prefixWord ++ tailWord_7036387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036387).length < 2 ^ (prefixWord ++ tailWord_7036387).sum := by decide
  have hdescent : baseEnd_7036387 < baseStart_7036387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036509 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7036509 : Nat := 118140960795 + 7036509 * 2 ^ 59
def prefixEnd_7036509 : Nat := 4983230072969 + 3 ^ 40 * 7036509 * 2
def baseEnd_7036509 : Nat := 3613111246687715359877191

theorem tailTrace_7036509 : CollatzResearch.WordTrace tailWord_7036509 prefixEnd_7036509 3613111246687715359877191 := by
  unfold tailWord_7036509
  simp only [CollatzResearch.WordTrace]
  refine ⟨256642567264937107906896581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171095044843291405271264387 256642567264937107906896581)
  ·
    refine ⟨48120481362175707732543109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256642567264937107906896581 48120481362175707732543109)
    ·
      refine ⟨9022590255407945199851833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48120481362175707732543109 9022590255407945199851833)
      ·
        refine ⟨6766942691555958899888875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9022590255407945199851833 6766942691555958899888875)
        ·
          refine ⟨10150414037333938349833313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6766942691555958899888875 10150414037333938349833313)
          ·
            refine ⟨7612810528000453762374985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10150414037333938349833313 7612810528000453762374985)
            ·
              refine ⟨5709607896000340321781239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612810528000453762374985 5709607896000340321781239)
              ·
                refine ⟨8564411844000510482671859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709607896000340321781239 8564411844000510482671859)
                ·
                  refine ⟨12846617766000765724007789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564411844000510482671859 12846617766000765724007789)
                  ·
                    refine ⟨4817481662250287146502921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12846617766000765724007789 4817481662250287146502921)
                    ·
                      refine ⟨3613111246687715359877191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817481662250287146502921 3613111246687715359877191)
                      ·
                        rfl

theorem cell23_7036509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7036509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036509 prefixEnd_7036509 := by exact prefixLift 7036509
  have htrace : WordTrace (prefixWord ++ tailWord_7036509) baseStart_7036509 baseEnd_7036509 := by
    simpa [prefixWord, tailWord_7036509, baseEnd_7036509] using wordTrace_append hprefix tailTrace_7036509
  have hstable : (prefixWord ++ tailWord_7036509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036509).length < 2 ^ (prefixWord ++ tailWord_7036509).sum := by decide
  have hdescent : baseEnd_7036509 < baseStart_7036509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036601 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 6]
def baseStart_7036601 : Nat := 118140960795 + 7036601 * 2 ^ 59
def prefixEnd_7036601 : Nat := 4983230072969 + 3 ^ 40 * 7036601 * 2
def baseEnd_7036601 : Nat := 401462054100880999991863

theorem tailTrace_7036601 : CollatzResearch.WordTrace tailWord_7036601 prefixEnd_7036601 401462054100880999991863 := by
  unfold tailWord_7036601
  simp only [CollatzResearch.WordTrace]
  refine ⟨256645922780603807619245657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171097281853735871746163771 256645922780603807619245657)
  ·
    refine ⟨192484442085452855714434243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256645922780603807619245657 192484442085452855714434243)
    ·
      refine ⟨288726663128179283571651365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192484442085452855714434243 288726663128179283571651365)
      ·
        refine ⟨54136249336533615669684631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288726663128179283571651365 54136249336533615669684631)
        ·
          refine ⟨81204374004800423504526947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54136249336533615669684631 81204374004800423504526947)
          ·
            refine ⟨121806561007200635256790421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81204374004800423504526947 121806561007200635256790421)
            ·
              refine ⟨5709682547212529777662051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121806561007200635256790421 5709682547212529777662051)
              ·
                refine ⟨8564523820818794666493077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709682547212529777662051 8564523820818794666493077)
                ·
                  refine ⟨401462054100880999991863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8564523820818794666493077 401462054100880999991863)
                  ·
                    rfl

theorem cell23_7036601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 6].length) (baseStart_7036601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036601 prefixEnd_7036601 := by exact prefixLift 7036601
  have htrace : WordTrace (prefixWord ++ tailWord_7036601) baseStart_7036601 baseEnd_7036601 := by
    simpa [prefixWord, tailWord_7036601, baseEnd_7036601] using wordTrace_append hprefix tailTrace_7036601
  have hstable : (prefixWord ++ tailWord_7036601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036601).length < 2 ^ (prefixWord ++ tailWord_7036601).sum := by decide
  have hdescent : baseEnd_7036601 < baseStart_7036601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036644 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_7036644 : Nat := 118140960795 + 7036644 * 2 ^ 59
def prefixEnd_7036644 : Nat := 4983230072969 + 3 ^ 40 * 7036644 * 2
def baseEnd_7036644 : Nat := 1204393522192024110563023

theorem tailTrace_7036644 : CollatzResearch.WordTrace tailWord_7036644 prefixEnd_7036644 1204393522192024110563023 := by
  unfold tailWord_7036644
  simp only [CollatzResearch.WordTrace]
  refine ⟨128323745559724012981530493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171098327412965350642040657 128323745559724012981530493)
  ·
    refine ⟨48121404584896504868073935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128323745559724012981530493 48121404584896504868073935)
    ·
      refine ⟨72182106877344757302110903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48121404584896504868073935 72182106877344757302110903)
      ·
        refine ⟨108273160316017135953166355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72182106877344757302110903 108273160316017135953166355)
        ·
          refine ⟨162409740474025703929749533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108273160316017135953166355 162409740474025703929749533)
          ·
            refine ⟨60903652677759638973656075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162409740474025703929749533 60903652677759638973656075)
            ·
              refine ⟨91355479016639458460484113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60903652677759638973656075 91355479016639458460484113)
              ·
                refine ⟨68516609262479593845363085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91355479016639458460484113 68516609262479593845363085)
                ·
                  refine ⟨25693728473429847692011157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68516609262479593845363085 25693728473429847692011157)
                  ·
                    refine ⟨1204393522192024110563023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25693728473429847692011157 1204393522192024110563023)
                    ·
                      rfl

theorem cell23_7036644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_7036644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036644 prefixEnd_7036644 := by exact prefixLift 7036644
  have htrace : WordTrace (prefixWord ++ tailWord_7036644) baseStart_7036644 baseEnd_7036644 := by
    simpa [prefixWord, tailWord_7036644, baseEnd_7036644] using wordTrace_append hprefix tailTrace_7036644
  have hstable : (prefixWord ++ tailWord_7036644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036644).length < 2 ^ (prefixWord ++ tailWord_7036644).sum := by decide
  have hdescent : baseEnd_7036644 < baseStart_7036644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036645 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7036645 : Nat := 118140960795 + 7036645 * 2 ^ 59
def prefixEnd_7036645 : Nat := 4983230072969 + 3 ^ 40 * 7036645 * 2
def baseEnd_7036645 : Nat := 3613181080056726827776565

theorem tailTrace_7036645 : CollatzResearch.WordTrace tailWord_7036645 prefixEnd_7036645 3613181080056726827776565 := by
  unfold tailWord_7036645
  simp only [CollatzResearch.WordTrace]
  refine ⟨256647527592444403133847389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171098351728296268755898259 256647527592444403133847389)
  ·
    refine ⟨96242822847166651175192771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256647527592444403133847389 96242822847166651175192771)
    ·
      refine ⟨144364234270749976762789157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96242822847166651175192771 144364234270749976762789157)
      ·
        refine ⟨27068293925765620643022967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144364234270749976762789157 27068293925765620643022967)
        ·
          refine ⟨40602440888648430964534451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27068293925765620643022967 40602440888648430964534451)
          ·
            refine ⟨60903661332972646446801677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40602440888648430964534451 60903661332972646446801677)
            ·
              refine ⟨22838872999864742417550629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60903661332972646446801677 22838872999864742417550629)
              ·
                refine ⟨4282288687474639203290743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22838872999864742417550629 4282288687474639203290743)
                ·
                  refine ⟨6423433031211958804936115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282288687474639203290743 6423433031211958804936115)
                  ·
                    refine ⟨9635149546817938207404173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6423433031211958804936115 9635149546817938207404173)
                    ·
                      refine ⟨3613181080056726827776565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635149546817938207404173 3613181080056726827776565)
                      ·
                        rfl

theorem cell23_7036645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7036645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036645 prefixEnd_7036645 := by exact prefixLift 7036645
  have htrace : WordTrace (prefixWord ++ tailWord_7036645) baseStart_7036645 baseEnd_7036645 := by
    simpa [prefixWord, tailWord_7036645, baseEnd_7036645] using wordTrace_append hprefix tailTrace_7036645
  have hstable : (prefixWord ++ tailWord_7036645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036645).length < 2 ^ (prefixWord ++ tailWord_7036645).sum := by decide
  have hdescent : baseEnd_7036645 < baseStart_7036645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036671 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_7036671 : Nat := 118140960795 + 7036671 * 2 ^ 59
def prefixEnd_7036671 : Nat := 4983230072969 + 3 ^ 40 * 7036671 * 2
def baseEnd_7036671 : Nat := 3613194430553743726051445

theorem tailTrace_7036671 : CollatzResearch.WordTrace tailWord_7036671 prefixEnd_7036671 3613194430553743726051445 := by
  unfold tailWord_7036671
  simp only [CollatzResearch.WordTrace]
  refine ⟨256648475890350209574293867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171098983926900139716195911 256648475890350209574293867)
  ·
    refine ⟨384972713835525314361440801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256648475890350209574293867 384972713835525314361440801)
    ·
      refine ⟨288729535376643985771080601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384972713835525314361440801 288729535376643985771080601)
      ·
        refine ⟨216547151532482989328310451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288729535376643985771080601 216547151532482989328310451)
        ·
          refine ⟨324820727298724483992465677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216547151532482989328310451 324820727298724483992465677)
          ·
            refine ⟨121807772737021681497174629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324820727298724483992465677 121807772737021681497174629)
            ·
              refine ⟨22838957388191565280720243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121807772737021681497174629 22838957388191565280720243)
              ·
                refine ⟨34258436082287347921080365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22838957388191565280720243 34258436082287347921080365)
                ·
                  refine ⟨12846913530857755470405137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34258436082287347921080365 12846913530857755470405137)
                  ·
                    refine ⟨9635185148143316602803853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12846913530857755470405137 9635185148143316602803853)
                    ·
                      refine ⟨3613194430553743726051445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635185148143316602803853 3613194430553743726051445)
                      ·
                        rfl

theorem cell23_7036671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_7036671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036671 prefixEnd_7036671 := by exact prefixLift 7036671
  have htrace : WordTrace (prefixWord ++ tailWord_7036671) baseStart_7036671 baseEnd_7036671 := by
    simpa [prefixWord, tailWord_7036671, baseEnd_7036671] using wordTrace_append hprefix tailTrace_7036671
  have hstable : (prefixWord ++ tailWord_7036671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036671).length < 2 ^ (prefixWord ++ tailWord_7036671).sum := by decide
  have hdescent : baseEnd_7036671 < baseStart_7036671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036695 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 2, 4]
def baseStart_7036695 : Nat := 118140960795 + 7036695 * 2 ^ 59
def prefixEnd_7036695 : Nat := 4983230072969 + 3 ^ 40 * 7036695 * 2
def baseEnd_7036695 : Nat := 1204402251363150544050445

theorem tailTrace_7036695 : CollatzResearch.WordTrace tailWord_7036695 prefixEnd_7036695 1204402251363150544050445 := by
  unfold tailWord_7036695
  simp only [CollatzResearch.WordTrace]
  refine ⟨256649351242263261673167539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171099567494842174448778359 256649351242263261673167539)
  ·
    refine ⟨384974026863394892509751309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256649351242263261673167539 384974026863394892509751309)
    ·
      refine ⟨144365260073773084691156741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384974026863394892509751309 144365260073773084691156741)
      ·
        refine ⟨27068486263832453379591889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144365260073773084691156741 27068486263832453379591889)
        ·
          refine ⟨20301364697874340034693917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27068486263832453379591889 20301364697874340034693917)
          ·
            refine ⟨7613011761702877513010219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20301364697874340034693917 7613011761702877513010219)
            ·
              refine ⟨11419517642554316269515329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613011761702877513010219 11419517642554316269515329)
              ·
                refine ⟨8564638231915737202136497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11419517642554316269515329 8564638231915737202136497)
                ·
                  refine ⟨6423478673936802901602373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8564638231915737202136497 6423478673936802901602373)
                  ·
                    refine ⟨1204402251363150544050445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423478673936802901602373 1204402251363150544050445)
                    ·
                      rfl

theorem cell23_7036695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_7036695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036695 prefixEnd_7036695 := by exact prefixLift 7036695
  have htrace : WordTrace (prefixWord ++ tailWord_7036695) baseStart_7036695 baseEnd_7036695 := by
    simpa [prefixWord, tailWord_7036695, baseEnd_7036695] using wordTrace_append hprefix tailTrace_7036695
  have hstable : (prefixWord ++ tailWord_7036695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036695).length < 2 ^ (prefixWord ++ tailWord_7036695).sum := by decide
  have hdescent : baseEnd_7036695 < baseStart_7036695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036725 : List Nat := [1, 3, 3, 1, 5, 1, 2, 7]
def baseStart_7036725 : Nat := 118140960795 + 7036725 * 2 ^ 59
def prefixEnd_7036725 : Nat := 4983230072969 + 3 ^ 40 * 7036725 * 2
def baseEnd_7036725 : Nat := 133823042907743944991711

theorem tailTrace_7036725 : CollatzResearch.WordTrace tailWord_7036725 prefixEnd_7036725 133823042907743944991711 := by
  unfold tailWord_7036725
  simp only [CollatzResearch.WordTrace]
  refine ⟨256650445432154576796759629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171100296954769717864506419 256650445432154576796759629)
  ·
    refine ⟨96243917037057966298784861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256650445432154576796759629 96243917037057966298784861)
    ·
      refine ⟨36091468888896737362044323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96243917037057966298784861 36091468888896737362044323)
      ·
        refine ⟨54137203333345106043066485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091468888896737362044323 54137203333345106043066485)
        ·
          refine ⟨5075362812501103691537483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54137203333345106043066485 5075362812501103691537483)
          ·
            refine ⟨7613044218751655537306225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5075362812501103691537483 7613044218751655537306225)
            ·
              refine ⟨5709783164063741652979669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7613044218751655537306225 5709783164063741652979669)
              ·
                refine ⟨133823042907743944991711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5709783164063741652979669 133823042907743944991711)
                ·
                  rfl

theorem cell23_7036725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 7].length) (baseStart_7036725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036725 prefixEnd_7036725 := by exact prefixLift 7036725
  have htrace : WordTrace (prefixWord ++ tailWord_7036725) baseStart_7036725 baseEnd_7036725 := by
    simpa [prefixWord, tailWord_7036725, baseEnd_7036725] using wordTrace_append hprefix tailTrace_7036725
  have hstable : (prefixWord ++ tailWord_7036725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036725).length < 2 ^ (prefixWord ++ tailWord_7036725).sum := by decide
  have hdescent : baseEnd_7036725 < baseStart_7036725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036761 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_7036761 : Nat := 118140960795 + 7036761 * 2 ^ 59
def prefixEnd_7036761 : Nat := 4983230072969 + 3 ^ 40 * 7036761 * 2
def baseEnd_7036761 : Nat := 3613240643812648373926031

theorem tailTrace_7036761 : CollatzResearch.WordTrace tailWord_7036761 prefixEnd_7036761 3613240643812648373926031 := by
  unfold tailWord_7036761
  simp only [CollatzResearch.WordTrace]
  refine ⟨256651758460024154945070137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171101172306682769963380091 256651758460024154945070137)
  ·
    refine ⟨192488818845018116208802603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256651758460024154945070137 192488818845018116208802603)
    ·
      refine ⟨288733228267527174313203905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192488818845018116208802603 288733228267527174313203905)
      ·
        refine ⟨216549921200645380734902929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288733228267527174313203905 216549921200645380734902929)
        ·
          refine ⟨162412440900484035551177197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216549921200645380734902929 162412440900484035551177197)
          ·
            refine ⟨60904665337681513331691449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162412440900484035551177197 60904665337681513331691449)
            ·
              refine ⟨45678499003261134998768587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60904665337681513331691449 45678499003261134998768587)
              ·
                refine ⟨68517748504891702498152881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45678499003261134998768587 68517748504891702498152881)
                ·
                  refine ⟨51388311378668776873614661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68517748504891702498152881 51388311378668776873614661)
                  ·
                    refine ⟨9635308383500395663802749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51388311378668776873614661 9635308383500395663802749)
                    ·
                      refine ⟨3613240643812648373926031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635308383500395663802749 3613240643812648373926031)
                      ·
                        rfl

theorem cell23_7036761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_7036761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036761 prefixEnd_7036761 := by exact prefixLift 7036761
  have htrace : WordTrace (prefixWord ++ tailWord_7036761) baseStart_7036761 baseEnd_7036761 := by
    simpa [prefixWord, tailWord_7036761, baseEnd_7036761] using wordTrace_append hprefix tailTrace_7036761
  have hstable : (prefixWord ++ tailWord_7036761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036761).length < 2 ^ (prefixWord ++ tailWord_7036761).sum := by decide
  have hdescent : baseEnd_7036761 < baseStart_7036761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036781 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 7]
def baseStart_7036781 : Nat := 118140960795 + 7036781 * 2 ^ 59
def prefixEnd_7036781 : Nat := 4983230072969 + 3 ^ 40 * 7036781 * 2
def baseEnd_7036781 : Nat := 401472323713970921741771

theorem tailTrace_7036781 : CollatzResearch.WordTrace tailWord_7036781 prefixEnd_7036781 401472323713970921741771 := by
  unfold tailWord_7036781
  simp only [CollatzResearch.WordTrace]
  refine ⟨256652487919951698360798197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171101658613301132240532131 256652487919951698360798197)
  ·
    refine ⟨24061170742495471721324831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256652487919951698360798197 24061170742495471721324831)
    ·
      refine ⟨36091756113743207581987247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24061170742495471721324831 36091756113743207581987247)
      ·
        refine ⟨54137634170614811372980871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091756113743207581987247 54137634170614811372980871)
        ·
          refine ⟨81206451255922217059471307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54137634170614811372980871 81206451255922217059471307)
          ·
            refine ⟨121809676883883325589206961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81206451255922217059471307 121809676883883325589206961)
            ·
              refine ⟨91357257662912494191905221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121809676883883325589206961 91357257662912494191905221)
              ·
                refine ⟨17129485811796092660982229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91357257662912494191905221 17129485811796092660982229)
                ·
                  refine ⟨401472323713970921741771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17129485811796092660982229 401472323713970921741771)
                  ·
                    rfl

theorem cell23_7036781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_7036781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036781 prefixEnd_7036781 := by exact prefixLift 7036781
  have htrace : WordTrace (prefixWord ++ tailWord_7036781) baseStart_7036781 baseEnd_7036781 := by
    simpa [prefixWord, tailWord_7036781, baseEnd_7036781] using wordTrace_append hprefix tailTrace_7036781
  have hstable : (prefixWord ++ tailWord_7036781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036781).length < 2 ^ (prefixWord ++ tailWord_7036781).sum := by decide
  have hdescent : baseEnd_7036781 < baseStart_7036781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036791 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_7036791 : Nat := 118140960795 + 7036791 * 2 ^ 59
def prefixEnd_7036791 : Nat := 4983230072969 + 3 ^ 40 * 7036791 * 2
def baseEnd_7036791 : Nat := 3613256048232283256550893

theorem tailTrace_7036791 : CollatzResearch.WordTrace tailWord_7036791 prefixEnd_7036791 3613256048232283256550893 := by
  unfold tailWord_7036791
  simp only [CollatzResearch.WordTrace]
  refine ⟨256652852649915470068662227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171101901766610313379108151 256652852649915470068662227)
  ·
    refine ⟨384979278974873205102993341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256652852649915470068662227 384979278974873205102993341)
    ·
      refine ⟨144367229615577451913622503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384979278974873205102993341 144367229615577451913622503)
      ·
        refine ⟨216550844423366177870433755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144367229615577451913622503 216550844423366177870433755)
        ·
          refine ⟨324826266635049266805650633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216550844423366177870433755 324826266635049266805650633)
          ·
            refine ⟨243619699976286950104237975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324826266635049266805650633 243619699976286950104237975)
            ·
              refine ⟨365429549964430425156356963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243619699976286950104237975 365429549964430425156356963)
              ·
                refine ⟨548144324946645637734535445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365429549964430425156356963 548144324946645637734535445)
                ·
                  refine ⟨25694265231874014268806349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 548144324946645637734535445 25694265231874014268806349)
                  ·
                    refine ⟨9635349461952755350802381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25694265231874014268806349 9635349461952755350802381)
                    ·
                      refine ⟨3613256048232283256550893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635349461952755350802381 3613256048232283256550893)
                      ·
                        rfl

theorem cell23_7036791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_7036791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036791 prefixEnd_7036791 := by exact prefixLift 7036791
  have htrace : WordTrace (prefixWord ++ tailWord_7036791) baseStart_7036791 baseEnd_7036791 := by
    simpa [prefixWord, tailWord_7036791, baseEnd_7036791] using wordTrace_append hprefix tailTrace_7036791
  have hstable : (prefixWord ++ tailWord_7036791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036791).length < 2 ^ (prefixWord ++ tailWord_7036791).sum := by decide
  have hdescent : baseEnd_7036791 < baseStart_7036791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036821 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_7036821 : Nat := 118140960795 + 7036821 * 2 ^ 59
def prefixEnd_7036821 : Nat := 4983230072969 + 3 ^ 40 * 7036821 * 2
def baseEnd_7036821 : Nat := 3613271452651918139175755

theorem tailTrace_7036821 : CollatzResearch.WordTrace tailWord_7036821 prefixEnd_7036821 3613271452651918139175755 := by
  unfold tailWord_7036821
  simp only [CollatzResearch.WordTrace]
  refine ⟨256653946839806785192254317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171102631226537856794836211 256653946839806785192254317)
  ·
    refine ⟨96245230064927544447095369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256653946839806785192254317 96245230064927544447095369)
    ·
      refine ⟨72183922548695658335321527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96245230064927544447095369 72183922548695658335321527)
      ·
        refine ⟨108275883823043487502982291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72183922548695658335321527 108275883823043487502982291)
        ·
          refine ⟨162413825734565231254473437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108275883823043487502982291 162413825734565231254473437)
          ·
            refine ⟨60905184650461961720427539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162413825734565231254473437 60905184650461961720427539)
            ·
              refine ⟨91357776975692942580641309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60905184650461961720427539 91357776975692942580641309)
              ·
                refine ⟨34259166365884853467740491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91357776975692942580641309 34259166365884853467740491)
                ·
                  refine ⟨51388749548827280201610737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34259166365884853467740491 51388749548827280201610737)
                  ·
                    refine ⟨38541562161620460151208053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51388749548827280201610737 38541562161620460151208053)
                    ·
                      refine ⟨3613271452651918139175755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38541562161620460151208053 3613271452651918139175755)
                      ·
                        rfl

theorem cell23_7036821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_7036821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036821 prefixEnd_7036821 := by exact prefixLift 7036821
  have htrace : WordTrace (prefixWord ++ tailWord_7036821) baseStart_7036821 baseEnd_7036821 := by
    simpa [prefixWord, tailWord_7036821, baseEnd_7036821] using wordTrace_append hprefix tailTrace_7036821
  have hstable : (prefixWord ++ tailWord_7036821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036821).length < 2 ^ (prefixWord ++ tailWord_7036821).sum := by decide
  have hdescent : baseEnd_7036821 < baseStart_7036821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036875 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 1, 4]
def baseStart_7036875 : Nat := 118140960795 + 7036875 * 2 ^ 59
def prefixEnd_7036875 : Nat := 4983230072969 + 3 ^ 40 * 7036875 * 2
def baseEnd_7036875 : Nat := 1204433060202420309300169

theorem tailTrace_7036875 : CollatzResearch.WordTrace tailWord_7036875 prefixEnd_7036875 1204433060202420309300169 := by
  unfold tailWord_7036875
  simp only [CollatzResearch.WordTrace]
  refine ⟨256655916381611152414720079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171103944254407434943146719 256655916381611152414720079)
  ·
    refine ⟨384983874572416728622080119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256655916381611152414720079 384983874572416728622080119)
    ·
      refine ⟨577475811858625092933120179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384983874572416728622080119 577475811858625092933120179)
      ·
        refine ⟨866213717787937639399680269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577475811858625092933120179 866213717787937639399680269)
        ·
          refine ⟨324830144170476614774880101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866213717787937639399680269 324830144170476614774880101)
          ·
            refine ⟨60905652031964365270290019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324830144170476614774880101 60905652031964365270290019)
            ·
              refine ⟨91358478047946547905435029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60905652031964365270290019 91358478047946547905435029)
              ·
                refine ⟨4282428658497494433067267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91358478047946547905435029 4282428658497494433067267)
                ·
                  refine ⟨6423642987746241649600901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282428658497494433067267 6423642987746241649600901)
                  ·
                    refine ⟨1204433060202420309300169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423642987746241649600901 1204433060202420309300169)
                    ·
                      rfl

theorem cell23_7036875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 4].length) (baseStart_7036875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036875 prefixEnd_7036875 := by exact prefixLift 7036875
  have htrace : WordTrace (prefixWord ++ tailWord_7036875) baseStart_7036875 baseEnd_7036875 := by
    simpa [prefixWord, tailWord_7036875, baseEnd_7036875] using wordTrace_append hprefix tailTrace_7036875
  have hstable : (prefixWord ++ tailWord_7036875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036875).length < 2 ^ (prefixWord ++ tailWord_7036875).sum := by decide
  have hdescent : baseEnd_7036875 < baseStart_7036875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036925 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_7036925 : Nat := 118140960795 + 7036925 * 2 ^ 59
def prefixEnd_7036925 : Nat := 4983230072969 + 3 ^ 40 * 7036925 * 2
def baseEnd_7036925 : Nat := 3613324854639985732275277

theorem tailTrace_7036925 : CollatzResearch.WordTrace tailWord_7036925 prefixEnd_7036925 3613324854639985732275277 := by
  unfold tailWord_7036925
  simp only [CollatzResearch.WordTrace]
  refine ⟨256657740031430010954040229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171105160020953340636026819 256657740031430010954040229)
  ·
    refine ⟨48123326255893127053882543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256657740031430010954040229 48123326255893127053882543)
    ·
      refine ⟨72184989383839690580823815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48123326255893127053882543 72184989383839690580823815)
      ·
        refine ⟨108277484075759535871235723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72184989383839690580823815 108277484075759535871235723)
        ·
          refine ⟨162416226113639303806853585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108277484075759535871235723 162416226113639303806853585)
          ·
            refine ⟨121812169585229477855140189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162416226113639303806853585 121812169585229477855140189)
            ·
              refine ⟨45679563594461054195677571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121812169585229477855140189 45679563594461054195677571)
              ·
                refine ⟨68519345391691581293516357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45679563594461054195677571 68519345391691581293516357)
                ·
                  refine ⟨12847377260942171492534317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68519345391691581293516357 12847377260942171492534317)
                  ·
                    refine ⟨4817766472853314309700369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12847377260942171492534317 4817766472853314309700369)
                    ·
                      refine ⟨3613324854639985732275277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817766472853314309700369 3613324854639985732275277)
                      ·
                        rfl

theorem cell23_7036925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_7036925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036925 prefixEnd_7036925 := by exact prefixLift 7036925
  have htrace : WordTrace (prefixWord ++ tailWord_7036925) baseStart_7036925 baseEnd_7036925 := by
    simpa [prefixWord, tailWord_7036925, baseEnd_7036925] using wordTrace_append hprefix tailTrace_7036925
  have hstable : (prefixWord ++ tailWord_7036925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036925).length < 2 ^ (prefixWord ++ tailWord_7036925).sum := by decide
  have hdescent : baseEnd_7036925 < baseStart_7036925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7036926 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7036926 : Nat := 118140960795 + 7036926 * 2 ^ 59
def prefixEnd_7036926 : Nat := 4983230072969 + 3 ^ 40 * 7036926 * 2
def baseEnd_7036926 : Nat := 1204441789373546742787591

theorem tailTrace_7036926 : CollatzResearch.WordTrace tailWord_7036926 prefixEnd_7036926 1204441789373546742787591 := by
  unfold tailWord_7036926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32082222063053298515603329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171105184336284258749884421 32082222063053298515603329)
  ·
    refine ⟨24061666547289973886702497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32082222063053298515603329 24061666547289973886702497)
    ·
      refine ⟨18046249910467480415026873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24061666547289973886702497 18046249910467480415026873)
      ·
        refine ⟨13534687432850610311270155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18046249910467480415026873 13534687432850610311270155)
        ·
          refine ⟨20302031149275915466905233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13534687432850610311270155 20302031149275915466905233)
          ·
            refine ⟨15226523361956936600178925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20302031149275915466905233 15226523361956936600178925)
            ·
              refine ⟨5709946260733851225067097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15226523361956936600178925 5709946260733851225067097)
              ·
                refine ⟨4282459695550388418800323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709946260733851225067097 4282459695550388418800323)
                ·
                  refine ⟨6423689543325582628200485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282459695550388418800323 6423689543325582628200485)
                  ·
                    refine ⟨1204441789373546742787591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423689543325582628200485 1204441789373546742787591)
                    ·
                      rfl

theorem cell23_7036926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7036926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7036926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7036926 prefixEnd_7036926 := by exact prefixLift 7036926
  have htrace : WordTrace (prefixWord ++ tailWord_7036926) baseStart_7036926 baseEnd_7036926 := by
    simpa [prefixWord, tailWord_7036926, baseEnd_7036926] using wordTrace_append hprefix tailTrace_7036926
  have hstable : (prefixWord ++ tailWord_7036926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7036926).length < 2 ^ (prefixWord ++ tailWord_7036926).sum := by decide
  have hdescent : baseEnd_7036926 < baseStart_7036926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7036926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037018 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_7037018 : Nat := 118140960795 + 7037018 * 2 ^ 59
def prefixEnd_7037018 : Nat := 4983230072969 + 3 ^ 40 * 7037018 * 2
def baseEnd_7037018 : Nat := 3613372608340853868412349

theorem tailTrace_7037018 : CollatzResearch.WordTrace tailWord_7037018 prefixEnd_7037018 3613372608340853868412349 := by
  unfold tailWord_7037018
  simp only [CollatzResearch.WordTrace]
  refine ⟨64165283005023271959293927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171107421346728725224783805 64165283005023271959293927)
  ·
    refine ⟨96247924507534907938940891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64165283005023271959293927 96247924507534907938940891)
    ·
      refine ⟨144371886761302361908411337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96247924507534907938940891 144371886761302361908411337)
      ·
        refine ⟨108278915070976771431308503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144371886761302361908411337 108278915070976771431308503)
        ·
          refine ⟨162418372606465157146962755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108278915070976771431308503 162418372606465157146962755)
          ·
            refine ⟨243627558909697735720444133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162418372606465157146962755 243627558909697735720444133)
            ·
              refine ⟨45680167295568325447583275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243627558909697735720444133 45680167295568325447583275)
              ·
                refine ⟨68520250943352488171374913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45680167295568325447583275 68520250943352488171374913)
                ·
                  refine ⟨51390188207514366128531185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68520250943352488171374913 51390188207514366128531185)
                  ·
                    refine ⟨38542641155635774596398389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51390188207514366128531185 38542641155635774596398389)
                    ·
                      refine ⟨3613372608340853868412349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38542641155635774596398389 3613372608340853868412349)
                      ·
                        rfl

theorem cell23_7037018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_7037018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037018 prefixEnd_7037018 := by exact prefixLift 7037018
  have htrace : WordTrace (prefixWord ++ tailWord_7037018) baseStart_7037018 baseEnd_7037018 := by
    simpa [prefixWord, tailWord_7037018, baseEnd_7037018] using wordTrace_append hprefix tailTrace_7037018
  have hstable : (prefixWord ++ tailWord_7037018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037018).length < 2 ^ (prefixWord ++ tailWord_7037018).sum := by decide
  have hdescent : baseEnd_7037018 < baseStart_7037018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037039 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 3]
def baseStart_7037039 : Nat := 118140960795 + 7037039 * 2 ^ 59
def prefixEnd_7037039 : Nat := 4983230072969 + 3 ^ 40 * 7037039 * 2
def baseEnd_7037039 : Nat := 3613383391434598286249753

theorem tailTrace_7037039 : CollatzResearch.WordTrace tailWord_7037039 prefixEnd_7037039 3613383391434598286249753 := by
  unfold tailWord_7037039
  simp only [CollatzResearch.WordTrace]
  refine ⟨256661897953017008423690171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171107931968678005615793447 256661897953017008423690171)
  ·
    refine ⟨384992846929525512635535257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256661897953017008423690171 384992846929525512635535257)
    ·
      refine ⟨288744635197144134476651443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384992846929525512635535257 288744635197144134476651443)
      ·
        refine ⟨433116952795716201714977165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288744635197144134476651443 433116952795716201714977165)
        ·
          refine ⟨162418857298393575643116437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433116952795716201714977165 162418857298393575643116437)
          ·
            refine ⟨7613383935862198858271083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162418857298393575643116437 7613383935862198858271083)
            ·
              refine ⟨11420075903793298287406625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613383935862198858271083 11420075903793298287406625)
              ·
                refine ⟨8565056927844973715554969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11420075903793298287406625 8565056927844973715554969)
                ·
                  refine ⟨6423792695883730286666227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8565056927844973715554969 6423792695883730286666227)
                  ·
                    refine ⟨9635689043825595429999341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6423792695883730286666227 9635689043825595429999341)
                    ·
                      refine ⟨3613383391434598286249753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635689043825595429999341 3613383391434598286249753)
                      ·
                        rfl

theorem cell23_7037039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_7037039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037039 prefixEnd_7037039 := by exact prefixLift 7037039
  have htrace : WordTrace (prefixWord ++ tailWord_7037039) baseStart_7037039 baseEnd_7037039 := by
    simpa [prefixWord, tailWord_7037039, baseEnd_7037039] using wordTrace_append hprefix tailTrace_7037039
  have hstable : (prefixWord ++ tailWord_7037039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037039).length < 2 ^ (prefixWord ++ tailWord_7037039).sum := by decide
  have hdescent : baseEnd_7037039 < baseStart_7037039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037048 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_7037048 : Nat := 118140960795 + 7037048 * 2 ^ 59
def prefixEnd_7037048 : Nat := 4983230072969 + 3 ^ 40 * 7037048 * 2
def baseEnd_7037048 : Nat := 3613388012760488751037211

theorem tailTrace_7037048 : CollatzResearch.WordTrace tailWord_7037048 prefixEnd_7037048 3613388012760488751037211 := by
  unfold tailWord_7037048
  simp only [CollatzResearch.WordTrace]
  refine ⟨128331113104992201480383899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171108150806656268640511865 128331113104992201480383899)
  ·
    refine ⟨192496669657488302220575849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128331113104992201480383899 192496669657488302220575849)
    ·
      refine ⟨144372502243116226665431887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192496669657488302220575849 144372502243116226665431887)
      ·
        refine ⟨216558753364674339998147831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144372502243116226665431887 216558753364674339998147831)
        ·
          refine ⟨324838130047011509997221747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216558753364674339998147831 324838130047011509997221747)
          ·
            refine ⟨487257195070517264995832621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324838130047011509997221747 487257195070517264995832621)
            ·
              refine ⟨182721448151443974373437233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487257195070517264995832621 182721448151443974373437233)
              ·
                refine ⟨137041086113582980780077925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182721448151443974373437233 137041086113582980780077925)
                ·
                  refine ⟨25695203646296808896264611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137041086113582980780077925 25695203646296808896264611)
                  ·
                    refine ⟨38542805469445213344396917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25695203646296808896264611 38542805469445213344396917)
                    ·
                      refine ⟨3613388012760488751037211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38542805469445213344396917 3613388012760488751037211)
                      ·
                        rfl

theorem cell23_7037048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_7037048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037048 prefixEnd_7037048 := by exact prefixLift 7037048
  have htrace : WordTrace (prefixWord ++ tailWord_7037048) baseStart_7037048 baseEnd_7037048 := by
    simpa [prefixWord, tailWord_7037048, baseEnd_7037048] using wordTrace_append hprefix tailTrace_7037048
  have hstable : (prefixWord ++ tailWord_7037048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037048).length < 2 ^ (prefixWord ++ tailWord_7037048).sum := by decide
  have hdescent : baseEnd_7037048 < baseStart_7037048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037082 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7037082 : Nat := 118140960795 + 7037082 * 2 ^ 59
def prefixEnd_7037082 : Nat := 4983230072969 + 3 ^ 40 * 7037082 * 2
def baseEnd_7037082 : Nat := 3613405471102741618012055

theorem tailTrace_7037082 : CollatzResearch.WordTrace tailWord_7037082 prefixEnd_7037082 3613405471102741618012055 := by
  unfold tailWord_7037082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64165866572965306691876375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171108977527907484511670333 64165866572965306691876375)
  ·
    refine ⟨96248799859447960037814563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64165866572965306691876375 96248799859447960037814563)
    ·
      refine ⟨144373199789171940056721845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96248799859447960037814563 144373199789171940056721845)
      ·
        refine ⟨13534987480234869380317673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144373199789171940056721845 13534987480234869380317673)
        ·
          refine ⟨10151240610176152035238255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13534987480234869380317673 10151240610176152035238255)
          ·
            refine ⟨15226860915264228052857383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10151240610176152035238255 15226860915264228052857383)
            ·
              refine ⟨22840291372896342079286075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226860915264228052857383 22840291372896342079286075)
              ·
                refine ⟨34260437059344513118929113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22840291372896342079286075 34260437059344513118929113)
                ·
                  refine ⟨25695327794508384839196835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34260437059344513118929113 25695327794508384839196835)
                  ·
                    refine ⟨38542991691762577258795253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25695327794508384839196835 38542991691762577258795253)
                    ·
                      refine ⟨3613405471102741618012055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38542991691762577258795253 3613405471102741618012055)
                      ·
                        rfl

theorem cell23_7037082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7037082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037082 prefixEnd_7037082 := by exact prefixLift 7037082
  have htrace : WordTrace (prefixWord ++ tailWord_7037082) baseStart_7037082 baseEnd_7037082 := by
    simpa [prefixWord, tailWord_7037082, baseEnd_7037082] using wordTrace_append hprefix tailTrace_7037082
  have hstable : (prefixWord ++ tailWord_7037082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037082).length < 2 ^ (prefixWord ++ tailWord_7037082).sum := by decide
  have hdescent : baseEnd_7037082 < baseStart_7037082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037152 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2]
def baseStart_7037152 : Nat := 118140960795 + 7037152 * 2 ^ 59
def prefixEnd_7037152 : Nat := 4983230072969 + 3 ^ 40 * 7037152 * 2
def baseEnd_7037152 : Nat := 3613441414748556344136733

theorem tailTrace_7037152 : CollatzResearch.WordTrace tailWord_7037152 prefixEnd_7037152 3613441414748556344136733 := by
  unfold tailWord_7037152
  simp only [CollatzResearch.WordTrace]
  refine ⟨128333009700803814361276855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171110679601071752481702473 128333009700803814361276855)
  ·
    refine ⟨192499514551205721541915283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128333009700803814361276855 192499514551205721541915283)
    ·
      refine ⟨288749271826808582312872925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192499514551205721541915283 288749271826808582312872925)
      ·
        refine ⟨108280976935053218367327347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288749271826808582312872925 108280976935053218367327347)
        ·
          refine ⟨162421465402579827550991021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108280976935053218367327347 162421465402579827550991021)
          ·
            refine ⟨60908049525967435331621633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162421465402579827550991021 60908049525967435331621633)
            ·
              refine ⟨45681037144475576498716225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60908049525967435331621633 45681037144475576498716225)
              ·
                refine ⟨34260777858356682374037169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45681037144475576498716225 34260777858356682374037169)
                ·
                  refine ⟨25695583393767511780527877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34260777858356682374037169 25695583393767511780527877)
                  ·
                    refine ⟨4817921886331408458848977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25695583393767511780527877 4817921886331408458848977)
                    ·
                      refine ⟨3613441414748556344136733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4817921886331408458848977 3613441414748556344136733)
                      ·
                        rfl

theorem cell23_7037152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_7037152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037152 prefixEnd_7037152 := by exact prefixLift 7037152
  have htrace : WordTrace (prefixWord ++ tailWord_7037152) baseStart_7037152 baseEnd_7037152 := by
    simpa [prefixWord, tailWord_7037152, baseEnd_7037152] using wordTrace_append hprefix tailTrace_7037152
  have hstable : (prefixWord ++ tailWord_7037152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037152).length < 2 ^ (prefixWord ++ tailWord_7037152).sum := by decide
  have hdescent : baseEnd_7037152 < baseStart_7037152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037162 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7037162 : Nat := 118140960795 + 7037162 * 2 ^ 59
def prefixEnd_7037162 : Nat := 4983230072969 + 3 ^ 40 * 7037162 * 2
def baseEnd_7037162 : Nat := 1204482183185033768337229

theorem tailTrace_7037162 : CollatzResearch.WordTrace tailWord_7037162 prefixEnd_7037162 1204482183185033768337229 := by
  unfold tailWord_7037162
  simp only [CollatzResearch.WordTrace]
  refine ⟨64166596032892850107604435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171110922754380933620278493 64166596032892850107604435)
  ·
    refine ⟨96249894049339275161406653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64166596032892850107604435 96249894049339275161406653)
    ·
      refine ⟨36093710268502228185527495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96249894049339275161406653 36093710268502228185527495)
      ·
        refine ⟨54140565402753342278291243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36093710268502228185527495 54140565402753342278291243)
        ·
          refine ⟨81210848104130013417436865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54140565402753342278291243 81210848104130013417436865)
          ·
            refine ⟨60908136078097510063077649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81210848104130013417436865 60908136078097510063077649)
            ·
              refine ⟨45681102058573132547308237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60908136078097510063077649 45681102058573132547308237)
              ·
                refine ⟨17130413271964924705240589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45681102058573132547308237 17130413271964924705240589)
                ·
                  refine ⟨6423904976986846764465221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17130413271964924705240589 6423904976986846764465221)
                  ·
                    refine ⟨1204482183185033768337229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423904976986846764465221 1204482183185033768337229)
                    ·
                      rfl

theorem cell23_7037162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7037162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037162 prefixEnd_7037162 := by exact prefixLift 7037162
  have htrace : WordTrace (prefixWord ++ tailWord_7037162) baseStart_7037162 baseEnd_7037162 := by
    simpa [prefixWord, tailWord_7037162, baseEnd_7037162] using wordTrace_append hprefix tailTrace_7037162
  have hstable : (prefixWord ++ tailWord_7037162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037162).length < 2 ^ (prefixWord ++ tailWord_7037162).sum := by decide
  have hdescent : baseEnd_7037162 < baseStart_7037162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037186 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7037186 : Nat := 118140960795 + 7037186 * 2 ^ 59
def prefixEnd_7037186 : Nat := 4983230072969 + 3 ^ 40 * 7037186 * 2
def baseEnd_7037186 : Nat := 3613458873090809211111577

theorem tailTrace_7037186 : CollatzResearch.WordTrace tailWord_7037186 prefixEnd_7037186 3613458873090809211111577 := by
  unfold tailWord_7037186
  simp only [CollatzResearch.WordTrace]
  refine ⟨64166814870871113132322853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171111506322322968352860941 64166814870871113132322853)
  ·
    refine ⟨12031277788288333712310535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64166814870871113132322853 12031277788288333712310535)
    ·
      refine ⟨18046916682432500568465803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031277788288333712310535 18046916682432500568465803)
      ·
        refine ⟨27070375023648750852698705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18046916682432500568465803 27070375023648750852698705)
        ·
          refine ⟨20302781267736563139524029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27070375023648750852698705 20302781267736563139524029)
          ·
            refine ⟨7613542975401211177321511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20302781267736563139524029 7613542975401211177321511)
            ·
              refine ⟨11420314463101816765982267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613542975401211177321511 11420314463101816765982267)
              ·
                refine ⟨17130471694652725148973401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11420314463101816765982267 17130471694652725148973401)
                ·
                  refine ⟨12847853770989543861730051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17130471694652725148973401 12847853770989543861730051)
                  ·
                    refine ⟨19271780656484315792595077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12847853770989543861730051 19271780656484315792595077)
                    ·
                      refine ⟨3613458873090809211111577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19271780656484315792595077 3613458873090809211111577)
                      ·
                        rfl

theorem cell23_7037186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7037186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037186 prefixEnd_7037186 := by exact prefixLift 7037186
  have htrace : WordTrace (prefixWord ++ tailWord_7037186) baseStart_7037186 baseEnd_7037186 := by
    simpa [prefixWord, tailWord_7037186, baseEnd_7037186] using wordTrace_append hprefix tailTrace_7037186
  have hstable : (prefixWord ++ tailWord_7037186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037186).length < 2 ^ (prefixWord ++ tailWord_7037186).sum := by decide
  have hdescent : baseEnd_7037186 < baseStart_7037186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037219 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 3]
def baseStart_7037219 : Nat := 118140960795 + 7037219 * 2 ^ 59
def prefixEnd_7037219 : Nat := 4983230072969 + 3 ^ 40 * 7037219 * 2
def baseEnd_7037219 : Nat := 3613475817952407581998925

theorem tailTrace_7037219 : CollatzResearch.WordTrace tailWord_7037219 prefixEnd_7037219 3613475817952407581998925 := by
  unfold tailWord_7037219
  simp only [CollatzResearch.WordTrace]
  refine ⟨256668463092364899165242711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171112308728243266110161807 256668463092364899165242711)
  ·
    refine ⟨385002694638547348747864067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256668463092364899165242711 385002694638547348747864067)
    ·
      refine ⟨577504041957821023121796101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385002694638547348747864067 577504041957821023121796101)
      ·
        refine ⟨108282007867091441835336769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 577504041957821023121796101 108282007867091441835336769)
        ·
          refine ⟨81211505900318581376502577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108282007867091441835336769 81211505900318581376502577)
          ·
            refine ⟨60908629425238936032376933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81211505900318581376502577 60908629425238936032376933)
            ·
              refine ⟨11420368017232300506070675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60908629425238936032376933 11420368017232300506070675)
              ·
                refine ⟨17130552025848450759106013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11420368017232300506070675 17130552025848450759106013)
                ·
                  refine ⟨6423957009693169034664755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17130552025848450759106013 6423957009693169034664755)
                  ·
                    refine ⟨9635935514539753551997133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6423957009693169034664755 9635935514539753551997133)
                    ·
                      refine ⟨3613475817952407581998925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635935514539753551997133 3613475817952407581998925)
                      ·
                        rfl

theorem cell23_7037219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_7037219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037219 prefixEnd_7037219 := by exact prefixLift 7037219
  have htrace : WordTrace (prefixWord ++ tailWord_7037219) baseStart_7037219 baseEnd_7037219 := by
    simpa [prefixWord, tailWord_7037219, baseEnd_7037219] using wordTrace_append hprefix tailTrace_7037219
  have hstable : (prefixWord ++ tailWord_7037219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037219).length < 2 ^ (prefixWord ++ tailWord_7037219).sum := by decide
  have hdescent : baseEnd_7037219 < baseStart_7037219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037226 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_7037226 : Nat := 118140960795 + 7037226 * 2 ^ 59
def prefixEnd_7037226 : Nat := 4983230072969 + 3 ^ 40 * 7037226 * 2
def baseEnd_7037226 : Nat := 401497712479665450512377

theorem tailTrace_7037226 : CollatzResearch.WordTrace tailWord_7037226 prefixEnd_7037226 401497712479665450512377 := by
  unfold tailWord_7037226
  simp only [CollatzResearch.WordTrace]
  refine ⟨64167179600834884840186883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171112478935559692907165021 64167179600834884840186883)
  ·
    refine ⟨96250769401252327260280325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64167179600834884840186883 96250769401252327260280325)
    ·
      refine ⟨18047019262734811361302561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96250769401252327260280325 18047019262734811361302561)
      ·
        refine ⟨13535264447051108520976921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18047019262734811361302561 13535264447051108520976921)
        ·
          refine ⟨10151448335288331390732691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13535264447051108520976921 10151448335288331390732691)
          ·
            refine ⟨15227172502932497086099037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10151448335288331390732691 15227172502932497086099037)
            ·
              refine ⟨5710189688599686407287139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15227172502932497086099037 5710189688599686407287139)
              ·
                refine ⟨8565284532899529610930709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710189688599686407287139 8565284532899529610930709)
                ·
                  refine ⟨401497712479665450512377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8565284532899529610930709 401497712479665450512377)
                  ·
                    rfl

theorem cell23_7037226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_7037226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037226 prefixEnd_7037226 := by exact prefixLift 7037226
  have htrace : WordTrace (prefixWord ++ tailWord_7037226) baseStart_7037226 baseEnd_7037226 := by
    simpa [prefixWord, tailWord_7037226, baseEnd_7037226] using wordTrace_append hprefix tailTrace_7037226
  have hstable : (prefixWord ++ tailWord_7037226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037226).length < 2 ^ (prefixWord ++ tailWord_7037226).sum := by decide
  have hdescent : baseEnd_7037226 < baseStart_7037226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037236 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7037236 : Nat := 118140960795 + 7037236 * 2 ^ 59
def prefixEnd_7037236 : Nat := 4983230072969 + 3 ^ 40 * 7037236 * 2
def baseEnd_7037236 : Nat := 3613484547123534015486347

theorem tailTrace_7037236 : CollatzResearch.WordTrace tailWord_7037236 prefixEnd_7037236 3613484547123534015486347 := by
  unfold tailWord_7037236
  simp only [CollatzResearch.WordTrace]
  refine ⟨128334541566651655534305781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171112722088868874045741041 128334541566651655534305781)
  ·
    refine ⟨12031363271873592706341167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128334541566651655534305781 12031363271873592706341167)
    ·
      refine ⟨18047044907810389059511751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031363271873592706341167 18047044907810389059511751)
      ·
        refine ⟨27070567361715583589267627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18047044907810389059511751 27070567361715583589267627)
        ·
          refine ⟨40605851042573375383901441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27070567361715583589267627 40605851042573375383901441)
          ·
            refine ⟨30454388281930031537926081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40605851042573375383901441 30454388281930031537926081)
            ·
              refine ⟨22840791211447523653444561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30454388281930031537926081 22840791211447523653444561)
              ·
                refine ⟨17130593408585642740083421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22840791211447523653444561 17130593408585642740083421)
                ·
                  refine ⟨6423972528219616027531283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17130593408585642740083421 6423972528219616027531283)
                  ·
                    refine ⟨9635958792329424041296925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6423972528219616027531283 9635958792329424041296925)
                    ·
                      refine ⟨3613484547123534015486347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9635958792329424041296925 3613484547123534015486347)
                      ·
                        rfl

theorem cell23_7037236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7037236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037236 prefixEnd_7037236 := by exact prefixLift 7037236
  have htrace : WordTrace (prefixWord ++ tailWord_7037236) baseStart_7037236 baseEnd_7037236 := by
    simpa [prefixWord, tailWord_7037236, baseEnd_7037236] using wordTrace_append hprefix tailTrace_7037236
  have hstable : (prefixWord ++ tailWord_7037236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037236).length < 2 ^ (prefixWord ++ tailWord_7037236).sum := by decide
  have hdescent : baseEnd_7037236 < baseStart_7037236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037265 : List Nat := [1, 2, 2, 1, 4, 2, 11]
def baseStart_7037265 : Nat := 118140960795 + 7037265 * 2 ^ 59
def prefixEnd_7037265 : Nat := 4983230072969 + 3 ^ 40 * 7037265 * 2
def baseEnd_7037265 : Nat := 44611104173611288913873

theorem tailTrace_7037265 : CollatzResearch.WordTrace tailWord_7037265 prefixEnd_7037265 44611104173611288913873 := by
  unfold tailWord_7037265
  simp only [CollatzResearch.WordTrace]
  refine ⟨256670140850198249021417249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171113427233465499347611499 256670140850198249021417249)
  ·
    refine ⟨192502605637648686766062937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256670140850198249021417249 192502605637648686766062937)
    ·
      refine ⟨144376954228236515074547203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192502605637648686766062937 144376954228236515074547203)
      ·
        refine ⟨216565431342354772611820805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144376954228236515074547203 216565431342354772611820805)
        ·
          refine ⟨40606018376691519864716401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216565431342354772611820805 40606018376691519864716401)
          ·
            refine ⟨30454513782518639898537301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40606018376691519864716401 30454513782518639898537301)
            ·
              refine ⟨44611104173611288913873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30454513782518639898537301 44611104173611288913873)
              ·
                rfl

theorem cell23_7037265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 11].length) (baseStart_7037265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037265 prefixEnd_7037265 := by exact prefixLift 7037265
  have htrace : WordTrace (prefixWord ++ tailWord_7037265) baseStart_7037265 baseEnd_7037265 := by
    simpa [prefixWord, tailWord_7037265, baseEnd_7037265] using wordTrace_append hprefix tailTrace_7037265
  have hstable : (prefixWord ++ tailWord_7037265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037265).length < 2 ^ (prefixWord ++ tailWord_7037265).sum := by decide
  have hdescent : baseEnd_7037265 < baseStart_7037265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037282 : List Nat := [3, 3, 2, 1, 1, 2, 1, 10]
def baseStart_7037282 : Nat := 118140960795 + 7037282 * 2 ^ 59
def prefixEnd_7037282 : Nat := 4983230072969 + 3 ^ 40 * 7037282 * 2
def baseEnd_7037282 : Nat := 133833635823468179093005

theorem tailTrace_7037282 : CollatzResearch.WordTrace tailWord_7037282 prefixEnd_7037282 133833635823468179093005 := by
  unfold tailWord_7037282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64167690222784165231196525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171113840594091107283190733 64167690222784165231196525)
  ·
    refine ⟨24062883833544061961698697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64167690222784165231196525 24062883833544061961698697)
    ·
      refine ⟨18047162875158046471274023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24062883833544061961698697 18047162875158046471274023)
      ·
        refine ⟨27070744312737069706911035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18047162875158046471274023 27070744312737069706911035)
        ·
          refine ⟨40606116469105604560366553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27070744312737069706911035 40606116469105604560366553)
          ·
            refine ⟨30454587351829203420274915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40606116469105604560366553 30454587351829203420274915)
            ·
              refine ⟨45681881027743805130412373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30454587351829203420274915 45681881027743805130412373)
              ·
                refine ⟨133833635823468179093005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45681881027743805130412373 133833635823468179093005)
                ·
                  rfl

theorem cell23_7037282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_7037282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037282 prefixEnd_7037282 := by exact prefixLift 7037282
  have htrace : WordTrace (prefixWord ++ tailWord_7037282) baseStart_7037282 baseEnd_7037282 := by
    simpa [prefixWord, tailWord_7037282, baseEnd_7037282] using wordTrace_append hprefix tailTrace_7037282
  have hstable : (prefixWord ++ tailWord_7037282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037282).length < 2 ^ (prefixWord ++ tailWord_7037282).sum := by decide
  have hdescent : baseEnd_7037282 < baseStart_7037282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037295 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 7]
def baseStart_7037295 : Nat := 118140960795 + 7037295 * 2 ^ 59
def prefixEnd_7037295 : Nat := 4983230072969 + 3 ^ 40 * 7037295 * 2
def baseEnd_7037295 : Nat := 1204504947494049761549525

theorem tailTrace_7037295 : CollatzResearch.WordTrace tailWord_7037295 prefixEnd_7037295 1204504947494049761549525 := by
  unfold tailWord_7037295
  simp only [CollatzResearch.WordTrace]
  refine ⟨256671235040089564145009339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171114156693393042763339559 256671235040089564145009339)
  ·
    refine ⟨385006852560134346217514009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256671235040089564145009339 385006852560134346217514009)
    ·
      refine ⟨288755139420100759663135507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385006852560134346217514009 288755139420100759663135507)
      ·
        refine ⟨433132709130151139494703261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288755139420100759663135507 433132709130151139494703261)
        ·
          refine ⟨162424765923806677310513723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433132709130151139494703261 162424765923806677310513723)
          ·
            refine ⟨243637148885710015965770585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162424765923806677310513723 243637148885710015965770585)
            ·
              refine ⟨182727861664282511974327939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243637148885710015965770585 182727861664282511974327939)
              ·
                refine ⟨274091792496423767961491909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182727861664282511974327939 274091792496423767961491909)
                ·
                  refine ⟨51392211093079456492779733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 274091792496423767961491909 51392211093079456492779733)
                  ·
                    refine ⟨1204504947494049761549525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51392211093079456492779733 1204504947494049761549525)
                    ·
                      rfl

theorem cell23_7037295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_7037295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037295 prefixEnd_7037295 := by exact prefixLift 7037295
  have htrace : WordTrace (prefixWord ++ tailWord_7037295) baseStart_7037295 baseEnd_7037295 := by
    simpa [prefixWord, tailWord_7037295, baseEnd_7037295] using wordTrace_append hprefix tailTrace_7037295
  have hstable : (prefixWord ++ tailWord_7037295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037295).length < 2 ^ (prefixWord ++ tailWord_7037295).sum := by decide
  have hdescent : baseEnd_7037295 < baseStart_7037295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037296 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_7037296 : Nat := 118140960795 + 7037296 * 2 ^ 59
def prefixEnd_7037296 : Nat := 4983230072969 + 3 ^ 40 * 7037296 * 2
def baseEnd_7037296 : Nat := 3613515355962803780736071

theorem tailTrace_7037296 : CollatzResearch.WordTrace tailWord_7037296 prefixEnd_7037296 3613515355962803780736071 := by
  unfold tailWord_7037296
  simp only [CollatzResearch.WordTrace]
  refine ⟨128335635756542970657897871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171114181008723960877197161 128335635756542970657897871)
  ·
    refine ⟨192503453634814455986846807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128335635756542970657897871 192503453634814455986846807)
    ·
      refine ⟨288755180452221683980270211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192503453634814455986846807 288755180452221683980270211)
      ·
        refine ⟨433132770678332525970405317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288755180452221683980270211 433132770678332525970405317)
        ·
          refine ⟨81212394502187348619450997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433132770678332525970405317 81212394502187348619450997)
          ·
            refine ⟨7613661984580063933073531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81212394502187348619450997 7613661984580063933073531)
            ·
              refine ⟨11420492976870095899610297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613661984580063933073531 11420492976870095899610297)
              ·
                refine ⟨8565369732652571924707723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11420492976870095899610297 8565369732652571924707723)
                ·
                  refine ⟨12848054598978857887061585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565369732652571924707723 12848054598978857887061585)
                  ·
                    refine ⟨9636040949234143415296189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12848054598978857887061585 9636040949234143415296189)
                    ·
                      refine ⟨3613515355962803780736071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636040949234143415296189 3613515355962803780736071)
                      ·
                        rfl

theorem cell23_7037296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_7037296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037296 prefixEnd_7037296 := by exact prefixLift 7037296
  have htrace : WordTrace (prefixWord ++ tailWord_7037296) baseStart_7037296 baseEnd_7037296 := by
    simpa [prefixWord, tailWord_7037296, baseEnd_7037296] using wordTrace_append hprefix tailTrace_7037296
  have hstable : (prefixWord ++ tailWord_7037296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037296).length < 2 ^ (prefixWord ++ tailWord_7037296).sum := by decide
  have hdescent : baseEnd_7037296 < baseStart_7037296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037309 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_7037309 : Nat := 118140960795 + 7037309 * 2 ^ 59
def prefixEnd_7037309 : Nat := 4983230072969 + 3 ^ 40 * 7037309 * 2
def baseEnd_7037309 : Nat := 3613522031211312229873511

theorem tailTrace_7037309 : CollatzResearch.WordTrace tailWord_7037309 prefixEnd_7037309 3613522031211312229873511 := by
  unfold tailWord_7037309
  simp only [CollatzResearch.WordTrace]
  refine ⟨256671745662038844536018981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171114497108025896357345987 256671745662038844536018981)
  ·
    refine ⟨48125952311632283350503559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256671745662038844536018981 48125952311632283350503559)
    ·
      refine ⟨72188928467448425025755339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48125952311632283350503559 72188928467448425025755339)
      ·
        refine ⟨108283392701172637538633009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72188928467448425025755339 108283392701172637538633009)
        ·
          refine ⟨81212544525879478153974757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108283392701172637538633009 81212544525879478153974757)
          ·
            refine ⟨15227352098602402153870267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81212544525879478153974757 15227352098602402153870267)
            ·
              refine ⟨22841028147903603230805401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15227352098602402153870267 22841028147903603230805401)
              ·
                refine ⟨17130771110927702423104051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22841028147903603230805401 17130771110927702423104051)
                ·
                  refine ⟨25696156666391553634656077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17130771110927702423104051 25696156666391553634656077)
                  ·
                    refine ⟨9636058749896832612996029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25696156666391553634656077 9636058749896832612996029)
                    ·
                      refine ⟨3613522031211312229873511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636058749896832612996029 3613522031211312229873511)
                      ·
                        rfl

theorem cell23_7037309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_7037309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037309 prefixEnd_7037309 := by exact prefixLift 7037309
  have htrace : WordTrace (prefixWord ++ tailWord_7037309) baseStart_7037309 baseEnd_7037309 := by
    simpa [prefixWord, tailWord_7037309, baseEnd_7037309] using wordTrace_append hprefix tailTrace_7037309
  have hstable : (prefixWord ++ tailWord_7037309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037309).length < 2 ^ (prefixWord ++ tailWord_7037309).sum := by decide
  have hdescent : baseEnd_7037309 < baseStart_7037309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037313 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7037313 : Nat := 118140960795 + 7037313 * 2 ^ 59
def prefixEnd_7037313 : Nat := 4983230072969 + 3 ^ 40 * 7037313 * 2
def baseEnd_7037313 : Nat := 3613524085133930214223493

theorem tailTrace_7037313 : CollatzResearch.WordTrace tailWord_7037313 prefixEnd_7037313 3613524085133930214223493 := by
  unfold tailWord_7037313
  simp only [CollatzResearch.WordTrace]
  refine ⟨256671891554024353219164593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171114594369349568812776395 256671891554024353219164593)
  ·
    refine ⟨192503918665518264914373445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256671891554024353219164593 192503918665518264914373445)
    ·
      refine ⟨36094484749784674671445021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192503918665518264914373445 36094484749784674671445021)
      ·
        refine ⟨13535431781169253001791883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36094484749784674671445021 13535431781169253001791883)
        ·
          refine ⟨20303147671753879502687825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13535431781169253001791883 20303147671753879502687825)
          ·
            refine ⟨15227360753815409627015869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20303147671753879502687825 15227360753815409627015869)
            ·
              refine ⟨5710260282680778610130951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15227360753815409627015869 5710260282680778610130951)
              ·
                refine ⟨8565390424021167915196427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710260282680778610130951 8565390424021167915196427)
                ·
                  refine ⟨12848085636031751872794641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565390424021167915196427 12848085636031751872794641)
                  ·
                    refine ⟨9636064227023813904595981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12848085636031751872794641 9636064227023813904595981)
                    ·
                      refine ⟨3613524085133930214223493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636064227023813904595981 3613524085133930214223493)
                      ·
                        rfl

theorem cell23_7037313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7037313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037313 prefixEnd_7037313 := by exact prefixLift 7037313
  have htrace : WordTrace (prefixWord ++ tailWord_7037313) baseStart_7037313 baseEnd_7037313 := by
    simpa [prefixWord, tailWord_7037313, baseEnd_7037313] using wordTrace_append hprefix tailTrace_7037313
  have hstable : (prefixWord ++ tailWord_7037313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037313).length < 2 ^ (prefixWord ++ tailWord_7037313).sum := by decide
  have hdescent : baseEnd_7037313 < baseStart_7037313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037336 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7037336 : Nat := 118140960795 + 7037336 * 2 ^ 59
def prefixEnd_7037336 : Nat := 4983230072969 + 3 ^ 40 * 7037336 * 2
def baseEnd_7037336 : Nat := 3613535895188983624235887

theorem tailTrace_7037336 : CollatzResearch.WordTrace tailWord_7037336 prefixEnd_7037336 3613535895188983624235887 := by
  unfold tailWord_7037336
  simp only [CollatzResearch.WordTrace]
  refine ⟨128336365216470514073625931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171115153621960685431501241 128336365216470514073625931)
  ·
    refine ⟨192504547824705771110438897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128336365216470514073625931 192504547824705771110438897)
    ·
      refine ⟨144378410868529328332829173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192504547824705771110438897 144378410868529328332829173)
      ·
        refine ⟨13535476018924624531202735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144378410868529328332829173 13535476018924624531202735)
        ·
          refine ⟨20303214028386936796804103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13535476018924624531202735 20303214028386936796804103)
          ·
            refine ⟨30454821042580405195206155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20303214028386936796804103 30454821042580405195206155)
            ·
              refine ⟨45682231563870607792809233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30454821042580405195206155 45682231563870607792809233)
              ·
                refine ⟨34261673672902955844606925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45682231563870607792809233 34261673672902955844606925)
                ·
                  refine ⟨12848127627338608441727597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34261673672902955844606925 12848127627338608441727597)
                  ·
                    refine ⟨4818047860251978165647849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12848127627338608441727597 4818047860251978165647849)
                    ·
                      refine ⟨3613535895188983624235887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818047860251978165647849 3613535895188983624235887)
                      ·
                        rfl

theorem cell23_7037336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7037336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037336 prefixEnd_7037336 := by exact prefixLift 7037336
  have htrace : WordTrace (prefixWord ++ tailWord_7037336) baseStart_7037336 baseEnd_7037336 := by
    simpa [prefixWord, tailWord_7037336, baseEnd_7037336] using wordTrace_append hprefix tailTrace_7037336
  have hstable : (prefixWord ++ tailWord_7037336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037336).length < 2 ^ (prefixWord ++ tailWord_7037336).sum := by decide
  have hdescent : baseEnd_7037336 < baseStart_7037336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037362 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7037362 : Nat := 118140960795 + 7037362 * 2 ^ 59
def prefixEnd_7037362 : Nat := 4983230072969 + 3 ^ 40 * 7037362 * 2
def baseEnd_7037362 : Nat := 3613549245686000522510767

theorem tailTrace_7037362 : CollatzResearch.WordTrace tailWord_7037362 prefixEnd_7037362 3613549245686000522510767 := by
  unfold tailWord_7037362
  simp only [CollatzResearch.WordTrace]
  refine ⟨64168419682711708646924585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171115785820564556391798893 64168419682711708646924585)
  ·
    refine ⟨48126314762033781485193439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64168419682711708646924585 48126314762033781485193439)
    ·
      refine ⟨72189472143050672227790159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48126314762033781485193439 72189472143050672227790159)
      ·
        refine ⟨108284208214576008341685239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72189472143050672227790159 108284208214576008341685239)
        ·
          refine ⟨162426312321864012512527859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108284208214576008341685239 162426312321864012512527859)
          ·
            refine ⟨243639468482796018768791789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162426312321864012512527859 243639468482796018768791789)
            ·
              refine ⟨91364800681048507038296921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243639468482796018768791789 91364800681048507038296921)
              ·
                refine ⟨68523600510786380278722691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91364800681048507038296921 68523600510786380278722691)
                ·
                  refine ⟨102785400766179570418084037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68523600510786380278722691 102785400766179570418084037)
                  ·
                    refine ⟨19272262643658669453390757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102785400766179570418084037 19272262643658669453390757)
                    ·
                      refine ⟨3613549245686000522510767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19272262643658669453390757 3613549245686000522510767)
                      ·
                        rfl

theorem cell23_7037362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7037362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037362 prefixEnd_7037362 := by exact prefixLift 7037362
  have htrace : WordTrace (prefixWord ++ tailWord_7037362) baseStart_7037362 baseEnd_7037362 := by
    simpa [prefixWord, tailWord_7037362, baseEnd_7037362] using wordTrace_append hprefix tailTrace_7037362
  have hstable : (prefixWord ++ tailWord_7037362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037362).length < 2 ^ (prefixWord ++ tailWord_7037362).sum := by decide
  have hdescent : baseEnd_7037362 < baseStart_7037362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037364 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7037364 : Nat := 118140960795 + 7037364 * 2 ^ 59
def prefixEnd_7037364 : Nat := 4983230072969 + 3 ^ 40 * 7037364 * 2
def baseEnd_7037364 : Nat := 3613550272647309514685759

theorem tailTrace_7037364 : CollatzResearch.WordTrace tailWord_7037364 prefixEnd_7037364 3613550272647309514685759 := by
  unfold tailWord_7037364
  simp only [CollatzResearch.WordTrace]
  refine ⟨128336875838419794464635573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171115834451226392619514097 128336875838419794464635573)
  ·
    refine ⟨12031582109851855731059585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128336875838419794464635573 12031582109851855731059585)
    ·
      refine ⟨9023686582388891798294689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12031582109851855731059585 9023686582388891798294689)
      ·
        refine ⟨6767764936791668848721017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9023686582388891798294689 6767764936791668848721017)
        ·
          refine ⟨5075823702593751636540763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6767764936791668848721017 5075823702593751636540763)
          ·
            refine ⟨7613735553890627454811145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5075823702593751636540763 7613735553890627454811145)
            ·
              refine ⟨5710301665417970591108359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7613735553890627454811145 5710301665417970591108359)
              ·
                refine ⟨8565452498126955886662539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710301665417970591108359 8565452498126955886662539)
                ·
                  refine ⟨12848178747190433829993809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565452498126955886662539 12848178747190433829993809)
                  ·
                    refine ⟨9636134060392825372495357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12848178747190433829993809 9636134060392825372495357)
                    ·
                      refine ⟨3613550272647309514685759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636134060392825372495357 3613550272647309514685759)
                      ·
                        rfl

theorem cell23_7037364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7037364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037364 prefixEnd_7037364 := by exact prefixLift 7037364
  have htrace : WordTrace (prefixWord ++ tailWord_7037364) baseStart_7037364 baseEnd_7037364 := by
    simpa [prefixWord, tailWord_7037364, baseEnd_7037364] using wordTrace_append hprefix tailTrace_7037364
  have hstable : (prefixWord ++ tailWord_7037364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037364).length < 2 ^ (prefixWord ++ tailWord_7037364).sum := by decide
  have hdescent : baseEnd_7037364 < baseStart_7037364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037383 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_7037383 : Nat := 118140960795 + 7037383 * 2 ^ 59
def prefixEnd_7037383 : Nat := 4983230072969 + 3 ^ 40 * 7037383 * 2
def baseEnd_7037383 : Nat := 3613560028779744940348171

theorem tailTrace_7037383 : CollatzResearch.WordTrace tailWord_7037383 prefixEnd_7037383 3613560028779744940348171 := by
  unfold tailWord_7037383
  simp only [CollatzResearch.WordTrace]
  refine ⟨256674444663770755174212803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171116296442513836782808535 256674444663770755174212803)
  ·
    refine ⟨385011666995656132761319205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256674444663770755174212803 385011666995656132761319205)
    ·
      refine ⟨72189687561685524892747351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 385011666995656132761319205 72189687561685524892747351)
      ·
        refine ⟨108284531342528287339121027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72189687561685524892747351 108284531342528287339121027)
        ·
          refine ⟨162426797013792431008681541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108284531342528287339121027 162426797013792431008681541)
          ·
            refine ⟨30455024440086080814127789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162426797013792431008681541 30455024440086080814127789)
            ·
              refine ⟨11420634165032280305297921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30455024440086080814127789 11420634165032280305297921)
              ·
                refine ⟨8565475623774210228973441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11420634165032280305297921 8565475623774210228973441)
                ·
                  refine ⟨6424106717830657671730081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8565475623774210228973441 6424106717830657671730081)
                  ·
                    refine ⟨4818080038372993253797561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424106717830657671730081 4818080038372993253797561)
                    ·
                      refine ⟨3613560028779744940348171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818080038372993253797561 3613560028779744940348171)
                      ·
                        rfl

theorem cell23_7037383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_7037383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037383 prefixEnd_7037383 := by exact prefixLift 7037383
  have htrace : WordTrace (prefixWord ++ tailWord_7037383) baseStart_7037383 baseEnd_7037383 := by
    simpa [prefixWord, tailWord_7037383, baseEnd_7037383] using wordTrace_append hprefix tailTrace_7037383
  have hstable : (prefixWord ++ tailWord_7037383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037383).length < 2 ^ (prefixWord ++ tailWord_7037383).sum := by decide
  have hdescent : baseEnd_7037383 < baseStart_7037383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037402 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_7037402 : Nat := 118140960795 + 7037402 * 2 ^ 59
def prefixEnd_7037402 : Nat := 4983230072969 + 3 ^ 40 * 7037402 * 2
def baseEnd_7037402 : Nat := 1204523261637393455336861

theorem tailTrace_7037402 : CollatzResearch.WordTrace tailWord_7037402 prefixEnd_7037402 1204523261637393455336861 := by
  unfold tailWord_7037402
  simp only [CollatzResearch.WordTrace]
  refine ⟨64168784412675480354788615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171116758433801280946102973 64168784412675480354788615)
  ·
    refine ⟨96253176619013220532182923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64168784412675480354788615 96253176619013220532182923)
    ·
      refine ⟨144379764928519830798274385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96253176619013220532182923 144379764928519830798274385)
      ·
        refine ⟨108284823696389873098705789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144379764928519830798274385 108284823696389873098705789)
        ·
          refine ⟨40606808886146202412014671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108284823696389873098705789 40606808886146202412014671)
          ·
            refine ⟨60910213329219303618022007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40606808886146202412014671 60910213329219303618022007)
            ·
              refine ⟨91365319993828955427033011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60910213329219303618022007 91365319993828955427033011)
              ·
                refine ⟨137047979990743433140549517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91365319993828955427033011 137047979990743433140549517)
                ·
                  refine ⟨51392992496528787427706069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137047979990743433140549517 51392992496528787427706069)
                  ·
                    refine ⟨1204523261637393455336861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51392992496528787427706069 1204523261637393455336861)
                    ·
                      rfl

theorem cell23_7037402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_7037402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037402 prefixEnd_7037402 := by exact prefixLift 7037402
  have htrace : WordTrace (prefixWord ++ tailWord_7037402) baseStart_7037402 baseEnd_7037402 := by
    simpa [prefixWord, tailWord_7037402, baseEnd_7037402] using wordTrace_append hprefix tailTrace_7037402
  have hstable : (prefixWord ++ tailWord_7037402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037402).length < 2 ^ (prefixWord ++ tailWord_7037402).sum := by decide
  have hdescent : baseEnd_7037402 < baseStart_7037402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037412 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7037412 : Nat := 118140960795 + 7037412 * 2 ^ 59
def prefixEnd_7037412 : Nat := 4983230072969 + 3 ^ 40 * 7037412 * 2
def baseEnd_7037412 : Nat := 3613574919718725326885537

theorem tailTrace_7037412 : CollatzResearch.WordTrace tailWord_7037412 prefixEnd_7037412 3613574919718725326885537 := by
  unfold tailWord_7037412
  simp only [CollatzResearch.WordTrace]
  refine ⟨128337751190332846563509245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171117001587110462084678993 128337751190332846563509245)
  ·
    refine ⟨48126656696374817461315967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128337751190332846563509245 48126656696374817461315967)
    ·
      refine ⟨72189985044562226191973951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48126656696374817461315967 72189985044562226191973951)
      ·
        refine ⟨108284977566843339287960927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72189985044562226191973951 108284977566843339287960927)
        ·
          refine ⟨162427466350265008931941391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108284977566843339287960927 162427466350265008931941391)
          ·
            refine ⟨243641199525397513397912087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162427466350265008931941391 243641199525397513397912087)
            ·
              refine ⟨365461799288096270096868131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243641199525397513397912087 365461799288096270096868131)
              ·
                refine ⟨548192698932144405145302197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365461799288096270096868131 548192698932144405145302197)
                ·
                  refine ⟨51393065524888537982372081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548192698932144405145302197 51393065524888537982372081)
                  ·
                    refine ⟨38544799143666403486779061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51393065524888537982372081 38544799143666403486779061)
                    ·
                      refine ⟨3613574919718725326885537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38544799143666403486779061 3613574919718725326885537)
                      ·
                        rfl

theorem cell23_7037412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7037412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037412 prefixEnd_7037412 := by exact prefixLift 7037412
  have htrace : WordTrace (prefixWord ++ tailWord_7037412) baseStart_7037412 baseEnd_7037412 := by
    simpa [prefixWord, tailWord_7037412, baseEnd_7037412] using wordTrace_append hprefix tailTrace_7037412
  have hstable : (prefixWord ++ tailWord_7037412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037412).length < 2 ^ (prefixWord ++ tailWord_7037412).sum := by decide
  have hdescent : baseEnd_7037412 < baseStart_7037412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037439 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_7037439 : Nat := 118140960795 + 7037439 * 2 ^ 59
def prefixEnd_7037439 : Nat := 4983230072969 + 3 ^ 40 * 7037439 * 2
def baseEnd_7037439 : Nat := 3613588783696396721247913

theorem tailTrace_7037439 : CollatzResearch.WordTrace tailWord_7037439 prefixEnd_7037439 3613588783696396721247913 := by
  unfold tailWord_7037439
  simp only [CollatzResearch.WordTrace]
  refine ⟨256676487151567876738251371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171117658101045251158834247 256676487151567876738251371)
  ·
    refine ⟨385014730727351815107377057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256676487151567876738251371 385014730727351815107377057)
    ·
      refine ⟨288761048045513861330532793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385014730727351815107377057 288761048045513861330532793)
      ·
        refine ⟨216570786034135395997899595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288761048045513861330532793 216570786034135395997899595)
        ·
          refine ⟨324856179051203093996849393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216570786034135395997899595 324856179051203093996849393)
          ·
            refine ⟨243642134288402320497637045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324856179051203093996849393 243642134288402320497637045)
            ·
              refine ⟨22841450089537717546653473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243642134288402320497637045 22841450089537717546653473)
              ·
                refine ⟨17131087567153288159990105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22841450089537717546653473 17131087567153288159990105)
                ·
                  refine ⟨12848315675364966119992579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17131087567153288159990105 12848315675364966119992579)
                  ·
                    refine ⟨19272473513047449179988869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12848315675364966119992579 19272473513047449179988869)
                    ·
                      refine ⟨3613588783696396721247913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19272473513047449179988869 3613588783696396721247913)
                      ·
                        rfl

theorem cell23_7037439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_7037439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037439 prefixEnd_7037439 := by exact prefixLift 7037439
  have htrace : WordTrace (prefixWord ++ tailWord_7037439) baseStart_7037439 baseEnd_7037439 := by
    simpa [prefixWord, tailWord_7037439, baseEnd_7037439] using wordTrace_append hprefix tailTrace_7037439
  have hstable : (prefixWord ++ tailWord_7037439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037439).length < 2 ^ (prefixWord ++ tailWord_7037439).sum := by decide
  have hdescent : baseEnd_7037439 < baseStart_7037439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037449 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_7037449 : Nat := 118140960795 + 7037449 * 2 ^ 59
def prefixEnd_7037449 : Nat := 4983230072969 + 3 ^ 40 * 7037449 * 2
def baseEnd_7037449 : Nat := 1204531306167647227374289

theorem tailTrace_7037449 : CollatzResearch.WordTrace tailWord_7037449 prefixEnd_7037449 1204531306167647227374289 := by
  unfold tailWord_7037449
  simp only [CollatzResearch.WordTrace]
  refine ⟨256676851881531648446115401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171117901254354432297410267 256676851881531648446115401)
  ·
    refine ⟨192507638911148736334586551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256676851881531648446115401 192507638911148736334586551)
    ·
      refine ⟨288761458366723104501879827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192507638911148736334586551 288761458366723104501879827)
      ·
        refine ⟨433142187550084656752819741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288761458366723104501879827 433142187550084656752819741)
        ·
          refine ⟨162428320331281746282307403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433142187550084656752819741 162428320331281746282307403)
          ·
            refine ⟨243642480496922619423461105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162428320331281746282307403 243642480496922619423461105)
            ·
              refine ⟨182731860372691964567595829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243642480496922619423461105 182731860372691964567595829)
              ·
                refine ⟨17131111909939871678212109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182731860372691964567595829 17131111909939871678212109)
                ·
                  refine ⟨6424166966227451879329541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131111909939871678212109 6424166966227451879329541)
                  ·
                    refine ⟨1204531306167647227374289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424166966227451879329541 1204531306167647227374289)
                    ·
                      rfl

theorem cell23_7037449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_7037449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037449 prefixEnd_7037449 := by exact prefixLift 7037449
  have htrace : WordTrace (prefixWord ++ tailWord_7037449) baseStart_7037449 baseEnd_7037449 := by
    simpa [prefixWord, tailWord_7037449, baseEnd_7037449] using wordTrace_append hprefix tailTrace_7037449
  have hstable : (prefixWord ++ tailWord_7037449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037449).length < 2 ^ (prefixWord ++ tailWord_7037449).sum := by decide
  have hdescent : baseEnd_7037449 < baseStart_7037449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037459 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3]
def baseStart_7037459 : Nat := 118140960795 + 7037459 * 2 ^ 59
def prefixEnd_7037459 : Nat := 4983230072969 + 3 ^ 40 * 7037459 * 2
def baseEnd_7037459 : Nat := 3613599053309486642997821

theorem tailTrace_7037459 : CollatzResearch.WordTrace tailWord_7037459 prefixEnd_7037459 3613599053309486642997821 := by
  unfold tailWord_7037459
  simp only [CollatzResearch.WordTrace]
  refine ⟨256677216611495420153979431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171118144407663613435986287 256677216611495420153979431)
  ·
    refine ⟨385015824917243130230969147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256677216611495420153979431 385015824917243130230969147)
    ·
      refine ⟨577523737375864695346453721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385015824917243130230969147 577523737375864695346453721)
      ·
        refine ⟨433142803031898521509840291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577523737375864695346453721 433142803031898521509840291)
        ·
          refine ⟨649714204547847782264760437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433142803031898521509840291 649714204547847782264760437)
          ·
            refine ⟨60910706676360729587321291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 649714204547847782264760437 60910706676360729587321291)
            ·
              refine ⟨91366060014541094380981937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60910706676360729587321291 91366060014541094380981937)
              ·
                refine ⟨68524545010905820785736453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91366060014541094380981937 68524545010905820785736453)
                ·
                  refine ⟨12848352189544841397325585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68524545010905820785736453 12848352189544841397325585)
                  ·
                    refine ⟨9636264142158631047994189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12848352189544841397325585 9636264142158631047994189)
                    ·
                      refine ⟨3613599053309486642997821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636264142158631047994189 3613599053309486642997821)
                      ·
                        rfl

theorem cell23_7037459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_7037459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037459 prefixEnd_7037459 := by exact prefixLift 7037459
  have htrace : WordTrace (prefixWord ++ tailWord_7037459) baseStart_7037459 baseEnd_7037459 := by
    simpa [prefixWord, tailWord_7037459, baseEnd_7037459] using wordTrace_append hprefix tailTrace_7037459
  have hstable : (prefixWord ++ tailWord_7037459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037459).length < 2 ^ (prefixWord ++ tailWord_7037459).sum := by decide
  have hdescent : baseEnd_7037459 < baseStart_7037459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037500 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_7037500 : Nat := 118140960795 + 7037500 * 2 ^ 59
def prefixEnd_7037500 : Nat := 4983230072969 + 3 ^ 40 * 7037500 * 2
def baseEnd_7037500 : Nat := 1204540035338773660861711

theorem tailTrace_7037500 : CollatzResearch.WordTrace tailWord_7037500 prefixEnd_7037500 1204540035338773660861711 := by
  unfold tailWord_7037500
  simp only [CollatzResearch.WordTrace]
  refine ⟨128339356002173442078110977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171119141336231256104147969 128339356002173442078110977)
  ·
    refine ⟨96254517001630081558583233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128339356002173442078110977 96254517001630081558583233)
    ·
      refine ⟨72190887751222561168937425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96254517001630081558583233 72190887751222561168937425)
      ·
        refine ⟨54143165813416920876703069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72190887751222561168937425 54143165813416920876703069)
        ·
          refine ⟨20303687180031345328763651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54143165813416920876703069 20303687180031345328763651)
          ·
            refine ⟨30455530770047017993145477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20303687180031345328763651 30455530770047017993145477)
            ·
              refine ⟨5710412019383815873714777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30455530770047017993145477 5710412019383815873714777)
              ·
                refine ⟨4282809014537861905286083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5710412019383815873714777 4282809014537861905286083)
                ·
                  refine ⟨6424213521806792857929125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282809014537861905286083 6424213521806792857929125)
                  ·
                    refine ⟨1204540035338773660861711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424213521806792857929125 1204540035338773660861711)
                    ·
                      rfl

theorem cell23_7037500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_7037500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037500 prefixEnd_7037500 := by exact prefixLift 7037500
  have htrace : WordTrace (prefixWord ++ tailWord_7037500) baseStart_7037500 baseEnd_7037500 := by
    simpa [prefixWord, tailWord_7037500, baseEnd_7037500] using wordTrace_append hprefix tailTrace_7037500
  have hstable : (prefixWord ++ tailWord_7037500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037500).length < 2 ^ (prefixWord ++ tailWord_7037500).sum := by decide
  have hdescent : baseEnd_7037500 < baseStart_7037500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037509 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_7037509 : Nat := 118140960795 + 7037509 * 2 ^ 59
def prefixEnd_7037509 : Nat := 4983230072969 + 3 ^ 40 * 7037509 * 2
def baseEnd_7037509 : Nat := 1204541575780737149124197

theorem tailTrace_7037509 : CollatzResearch.WordTrace tailWord_7037509 prefixEnd_7037509 1204541575780737149124197 := by
  unfold tailWord_7037509
  simp only [CollatzResearch.WordTrace]
  refine ⟨256679040261314278693299581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171119360174209519128866387 256679040261314278693299581)
  ·
    refine ⟨96254640097992854509987343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256679040261314278693299581 96254640097992854509987343)
    ·
      refine ⟨144381960146989281764981015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96254640097992854509987343 144381960146989281764981015)
      ·
        refine ⟨216572940220483922647471523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144381960146989281764981015 216572940220483922647471523)
        ·
          refine ⟨324859410330725883971207285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216572940220483922647471523 324859410330725883971207285)
          ·
            refine ⟨30455569718505551622300683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324859410330725883971207285 30455569718505551622300683)
            ·
              refine ⟨45683354577758327433451025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30455569718505551622300683 45683354577758327433451025)
              ·
                refine ⟨34262515933318745575088269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45683354577758327433451025 34262515933318745575088269)
                ·
                  refine ⟨12848443474994529590658101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34262515933318745575088269 12848443474994529590658101)
                  ·
                    refine ⟨1204541575780737149124197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12848443474994529590658101 1204541575780737149124197)
                    ·
                      rfl

theorem cell23_7037509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_7037509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037509 prefixEnd_7037509 := by exact prefixLift 7037509
  have htrace : WordTrace (prefixWord ++ tailWord_7037509) baseStart_7037509 baseEnd_7037509 := by
    simpa [prefixWord, tailWord_7037509, baseEnd_7037509] using wordTrace_append hprefix tailTrace_7037509
  have hstable : (prefixWord ++ tailWord_7037509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037509).length < 2 ^ (prefixWord ++ tailWord_7037509).sum := by decide
  have hdescent : baseEnd_7037509 < baseStart_7037509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037516 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7037516 : Nat := 118140960795 + 7037516 * 2 ^ 59
def prefixEnd_7037516 : Nat := 4983230072969 + 3 ^ 40 * 7037516 * 2
def baseEnd_7037516 : Nat := 3613628321706792919985059

theorem tailTrace_7037516 : CollatzResearch.WordTrace tailWord_7037516 prefixEnd_7037516 3613628321706792919985059 := by
  unfold tailWord_7037516
  simp only [CollatzResearch.WordTrace]
  refine ⟨128339647786144459444402201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171119530381525945925869601 128339647786144459444402201)
  ·
    refine ⟨96254735839608344583301651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128339647786144459444402201 96254735839608344583301651)
    ·
      refine ⟨144382103759412516874952477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96254735839608344583301651 144382103759412516874952477)
      ·
        refine ⟨54143288909779693828107179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144382103759412516874952477 54143288909779693828107179)
        ·
          refine ⟨81214933364669540742160769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54143288909779693828107179 81214933364669540742160769)
          ·
            refine ⟨60911200023502155556620577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81214933364669540742160769 60911200023502155556620577)
            ·
              refine ⟨45683400017626616667465433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60911200023502155556620577 45683400017626616667465433)
              ·
                refine ⟨34262550013219962500599075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45683400017626616667465433 34262550013219962500599075)
                ·
                  refine ⟨51393825019829943750898613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34262550013219962500599075 51393825019829943750898613)
                  ·
                    refine ⟨4818171095609057226646745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51393825019829943750898613 4818171095609057226646745)
                    ·
                      refine ⟨3613628321706792919985059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818171095609057226646745 3613628321706792919985059)
                      ·
                        rfl

theorem cell23_7037516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7037516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037516 prefixEnd_7037516 := by exact prefixLift 7037516
  have htrace : WordTrace (prefixWord ++ tailWord_7037516) baseStart_7037516 baseEnd_7037516 := by
    simpa [prefixWord, tailWord_7037516, baseEnd_7037516] using wordTrace_append hprefix tailTrace_7037516
  have hstable : (prefixWord ++ tailWord_7037516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037516).length < 2 ^ (prefixWord ++ tailWord_7037516).sum := by decide
  have hdescent : baseEnd_7037516 < baseStart_7037516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037539 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 1, 6]
def baseStart_7037539 : Nat := 118140960795 + 7037539 * 2 ^ 59
def prefixEnd_7037539 : Nat := 4983230072969 + 3 ^ 40 * 7037539 * 2
def baseEnd_7037539 : Nat := 1204546710587282109999151

theorem tailTrace_7037539 : CollatzResearch.WordTrace tailWord_7037539 prefixEnd_7037539 1204546710587282109999151 := by
  unfold tailWord_7037539
  simp only [CollatzResearch.WordTrace]
  refine ⟨256680134451205593816891671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171120089634137062544594447 256680134451205593816891671)
  ·
    refine ⟨385020201676808390725337507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256680134451205593816891671 385020201676808390725337507)
    ·
      refine ⟨577530302515212586088006261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385020201676808390725337507 577530302515212586088006261)
      ·
        refine ⟨54143465860801179945750587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 577530302515212586088006261 54143465860801179945750587)
        ·
          refine ⟨81215198791201769918625881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54143465860801179945750587 81215198791201769918625881)
          ·
            refine ⟨60911399093401327438969411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81215198791201769918625881 60911399093401327438969411)
            ·
              refine ⟨91367098640101991158454117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60911399093401327438969411 91367098640101991158454117)
              ·
                refine ⟨17131330995019123342210147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91367098640101991158454117 17131330995019123342210147)
                ·
                  refine ⟨25696996492528685013315221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17131330995019123342210147 25696996492528685013315221)
                  ·
                    refine ⟨1204546710587282109999151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25696996492528685013315221 1204546710587282109999151)
                    ·
                      rfl

theorem cell23_7037539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 6].length) (baseStart_7037539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037539 prefixEnd_7037539 := by exact prefixLift 7037539
  have htrace : WordTrace (prefixWord ++ tailWord_7037539) baseStart_7037539 baseEnd_7037539 := by
    simpa [prefixWord, tailWord_7037539, baseEnd_7037539] using wordTrace_append hprefix tailTrace_7037539
  have hstable : (prefixWord ++ tailWord_7037539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037539).length < 2 ^ (prefixWord ++ tailWord_7037539).sum := by decide
  have hdescent : baseEnd_7037539 < baseStart_7037539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037540 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_7037540 : Nat := 118140960795 + 7037540 * 2 ^ 59
def prefixEnd_7037540 : Nat := 4983230072969 + 3 ^ 40 * 7037540 * 2
def baseEnd_7037540 : Nat := 3613640645242500826084949

theorem tailTrace_7037540 : CollatzResearch.WordTrace tailWord_7037540 prefixEnd_7037540 3613640645242500826084949 := by
  unfold tailWord_7037540
  simp only [CollatzResearch.WordTrace]
  refine ⟨128340085462100985493839037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171120113949467980658452049 128340085462100985493839037)
  ·
    refine ⟨48127532048287869560189639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128340085462100985493839037 48127532048287869560189639)
    ·
      refine ⟨72191298072431804340284459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48127532048287869560189639 72191298072431804340284459)
      ·
        refine ⟨108286947108647706510426689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72191298072431804340284459 108286947108647706510426689)
        ·
          refine ⟨81215210331485779882820017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108286947108647706510426689 81215210331485779882820017)
          ·
            refine ⟨60911407748614334912115013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81215210331485779882820017 60911407748614334912115013)
            ·
              refine ⟨11420888952865187796021565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60911407748614334912115013 11420888952865187796021565)
              ·
                refine ⟨4282833357324445423508087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11420888952865187796021565 4282833357324445423508087)
                ·
                  refine ⟨6424250035986668135262131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282833357324445423508087 6424250035986668135262131)
                  ·
                    refine ⟨9636375053980002202893197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424250035986668135262131 9636375053980002202893197)
                    ·
                      refine ⟨3613640645242500826084949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636375053980002202893197 3613640645242500826084949)
                      ·
                        rfl

theorem cell23_7037540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_7037540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037540 prefixEnd_7037540 := by exact prefixLift 7037540
  have htrace : WordTrace (prefixWord ++ tailWord_7037540) baseStart_7037540 baseEnd_7037540 := by
    simpa [prefixWord, tailWord_7037540, baseEnd_7037540] using wordTrace_append hprefix tailTrace_7037540
  have hstable : (prefixWord ++ tailWord_7037540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037540).length < 2 ^ (prefixWord ++ tailWord_7037540).sum := by decide
  have hdescent : baseEnd_7037540 < baseStart_7037540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037559 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_7037559 : Nat := 118140960795 + 7037559 * 2 ^ 59
def prefixEnd_7037559 : Nat := 4983230072969 + 3 ^ 40 * 7037559 * 2
def baseEnd_7037559 : Nat := 3613650401374936251747361

theorem tailTrace_7037559 : CollatzResearch.WordTrace tailWord_7037559 prefixEnd_7037559 3613650401374936251747361 := by
  unfold tailWord_7037559
  simp only [CollatzResearch.WordTrace]
  refine ⟨256680863911133137232619731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171120575940755424821746487 256680863911133137232619731)
  ·
    refine ⟨385021295866699705848929597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256680863911133137232619731 385021295866699705848929597)
    ·
      refine ⟨144382985950012389693348599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385021295866699705848929597 144382985950012389693348599)
      ·
        refine ⟨216574478925018584540022899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144382985950012389693348599 216574478925018584540022899)
        ·
          refine ⟨324861718387527876810034349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216574478925018584540022899 324861718387527876810034349)
          ·
            refine ⟨121823144395322953803762881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324861718387527876810034349 121823144395322953803762881)
            ·
              refine ⟨91367358296492215352822161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121823144395322953803762881 91367358296492215352822161)
              ·
                refine ⟨68525518722369161514616621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91367358296492215352822161 68525518722369161514616621)
                ·
                  refine ⟨25697069520888435567981233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68525518722369161514616621 25697069520888435567981233)
                  ·
                    refine ⟨19272802140666326675985925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25697069520888435567981233 19272802140666326675985925)
                    ·
                      refine ⟨3613650401374936251747361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19272802140666326675985925 3613650401374936251747361)
                      ·
                        rfl

theorem cell23_7037559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_7037559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037559 prefixEnd_7037559 := by exact prefixLift 7037559
  have htrace : WordTrace (prefixWord ++ tailWord_7037559) baseStart_7037559 baseEnd_7037559 := by
    simpa [prefixWord, tailWord_7037559, baseEnd_7037559] using wordTrace_append hprefix tailTrace_7037559
  have hstable : (prefixWord ++ tailWord_7037559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037559).length < 2 ^ (prefixWord ++ tailWord_7037559).sum := by decide
  have hdescent : baseEnd_7037559 < baseStart_7037559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037569 : List Nat := [1, 2, 4, 2, 1, 1, 2, 10]
def baseStart_7037569 : Nat := 118140960795 + 7037569 * 2 ^ 59
def prefixEnd_7037569 : Nat := 4983230072969 + 3 ^ 40 * 7037569 * 2
def baseEnd_7037569 : Nat := 133839093932647452319345

theorem tailTrace_7037569 : CollatzResearch.WordTrace tailWord_7037569 prefixEnd_7037569 133839093932647452319345 := by
  unfold tailWord_7037569
  simp only [CollatzResearch.WordTrace]
  refine ⟨256681228641096908940483761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171120819094064605960322507 256681228641096908940483761)
  ·
    refine ⟨192510921480822681705362821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256681228641096908940483761 192510921480822681705362821)
    ·
      refine ⟨36095797777654252819755529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192510921480822681705362821 36095797777654252819755529)
      ·
        refine ⟨27071848333240689614816647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36095797777654252819755529 27071848333240689614816647)
        ·
          refine ⟨40607772499861034422224971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27071848333240689614816647 40607772499861034422224971)
          ·
            refine ⟨60911658749791551633337457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40607772499861034422224971 60911658749791551633337457)
            ·
              refine ⟨45683744062343663725003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60911658749791551633337457 45683744062343663725003093)
              ·
                refine ⟨133839093932647452319345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45683744062343663725003093 133839093932647452319345)
                ·
                  rfl

theorem cell23_7037569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 10].length) (baseStart_7037569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037569 prefixEnd_7037569 := by exact prefixLift 7037569
  have htrace : WordTrace (prefixWord ++ tailWord_7037569) baseStart_7037569 baseEnd_7037569 := by
    simpa [prefixWord, tailWord_7037569, baseEnd_7037569] using wordTrace_append hprefix tailTrace_7037569
  have hstable : (prefixWord ++ tailWord_7037569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037569).length < 2 ^ (prefixWord ++ tailWord_7037569).sum := by decide
  have hdescent : baseEnd_7037569 < baseStart_7037569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037586 : List Nat := [3, 2, 3, 1, 2, 2, 1, 9]
def baseStart_7037586 : Nat := 118140960795 + 7037586 * 2 ^ 59
def prefixEnd_7037586 : Nat := 4983230072969 + 3 ^ 40 * 7037586 * 2
def baseEnd_7037586 : Nat := 133839417235281764670731

theorem tailTrace_7037586 : CollatzResearch.WordTrace tailWord_7037586 prefixEnd_7037586 133839417235281764670731 := by
  unfold tailWord_7037586
  simp only [CollatzResearch.WordTrace]
  refine ⟨64170462170508830210963153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171121232454690213895901741 64170462170508830210963153)
  ·
    refine ⟨48127846627881622658222365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64170462170508830210963153 48127846627881622658222365)
    ·
      refine ⟨18047942485455608496833387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48127846627881622658222365 18047942485455608496833387)
      ·
        refine ⟨27071913728183412745250081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18047942485455608496833387 27071913728183412745250081)
        ·
          refine ⟨20303935296137559558937561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27071913728183412745250081 20303935296137559558937561)
          ·
            refine ⟨15227951472103169669203171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20303935296137559558937561 15227951472103169669203171)
            ·
              refine ⟨22841927208154754503804757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15227951472103169669203171 22841927208154754503804757)
              ·
                refine ⟨133839417235281764670731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22841927208154754503804757 133839417235281764670731)
                ·
                  rfl

theorem cell23_7037586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_7037586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037586 prefixEnd_7037586 := by exact prefixLift 7037586
  have htrace : WordTrace (prefixWord ++ tailWord_7037586) baseStart_7037586 baseEnd_7037586 := by
    simpa [prefixWord, tailWord_7037586, baseEnd_7037586] using wordTrace_append hprefix tailTrace_7037586
  have hstable : (prefixWord ++ tailWord_7037586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037586).length < 2 ^ (prefixWord ++ tailWord_7037586).sum := by decide
  have hdescent : baseEnd_7037586 < baseStart_7037586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037597 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_7037597 : Nat := 118140960795 + 7037597 * 2 ^ 59
def prefixEnd_7037597 : Nat := 4983230072969 + 3 ^ 40 * 7037597 * 2
def baseEnd_7037597 : Nat := 3613669913639807103072187

theorem tailTrace_7037597 : CollatzResearch.WordTrace tailWord_7037597 prefixEnd_7037597 3613669913639807103072187 := by
  unfold tailWord_7037597
  simp only [CollatzResearch.WordTrace]
  refine ⟨256682249884995469722503045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171121499923330313148335363 256682249884995469722503045)
  ·
    refine ⟨48127921853436650572969321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256682249884995469722503045 48127921853436650572969321)
    ·
      refine ⟨36095941390077487929726991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48127921853436650572969321 36095941390077487929726991)
      ·
        refine ⟨54143912085116231894590487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36095941390077487929726991 54143912085116231894590487)
        ·
          refine ⟨81215868127674347841885731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54143912085116231894590487 81215868127674347841885731)
          ·
            refine ⟨121823802191511521762828597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81215868127674347841885731 121823802191511521762828597)
            ·
              refine ⟨11420981455454205165265181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121823802191511521762828597 11420981455454205165265181)
              ·
                refine ⟨4282868045795326936974443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11420981455454205165265181 4282868045795326936974443)
                ·
                  refine ⟨6424302068692990405461665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282868045795326936974443 6424302068692990405461665)
                  ·
                    refine ⟨4818226551519742804096249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424302068692990405461665 4818226551519742804096249)
                    ·
                      refine ⟨3613669913639807103072187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818226551519742804096249 3613669913639807103072187)
                      ·
                        rfl

theorem cell23_7037597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_7037597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037597 prefixEnd_7037597 := by exact prefixLift 7037597
  have htrace : WordTrace (prefixWord ++ tailWord_7037597) baseStart_7037597 baseEnd_7037597 := by
    simpa [prefixWord, tailWord_7037597, baseEnd_7037597] using wordTrace_append hprefix tailTrace_7037597
  have hstable : (prefixWord ++ tailWord_7037597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037597).length < 2 ^ (prefixWord ++ tailWord_7037597).sum := by decide
  have hdescent : baseEnd_7037597 < baseStart_7037597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037614 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7037614 : Nat := 118140960795 + 7037614 * 2 ^ 59
def prefixEnd_7037614 : Nat := 4983230072969 + 3 ^ 40 * 7037614 * 2
def baseEnd_7037614 : Nat := 3613678642810933536559609

theorem tailTrace_7037614 : CollatzResearch.WordTrace tailWord_7037614 prefixEnd_7037614 3613678642810933536559609 := by
  unfold tailWord_7037614
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085358740741735203233987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171121913283955921083914597 32085358740741735203233987)
  ·
    refine ⟨48128038111112602804850981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32085358740741735203233987 48128038111112602804850981)
    ·
      refine ⟨9024007145833613025909559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48128038111112602804850981 9024007145833613025909559)
      ·
        refine ⟨13536010718750419538864339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024007145833613025909559 13536010718750419538864339)
        ·
          refine ⟨20304016078125629308296509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536010718750419538864339 20304016078125629308296509)
          ·
            refine ⟨7614006029297110990611191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20304016078125629308296509 7614006029297110990611191)
            ·
              refine ⟨11421009043945666485916787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614006029297110990611191 11421009043945666485916787)
              ·
                refine ⟨17131513565918499728875181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421009043945666485916787 17131513565918499728875181)
                ·
                  refine ⟨6424317587219437398328193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131513565918499728875181 6424317587219437398328193)
                  ·
                    refine ⟨4818238190414578048746145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424317587219437398328193 4818238190414578048746145)
                    ·
                      refine ⟨3613678642810933536559609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818238190414578048746145 3613678642810933536559609)
                      ·
                        rfl

theorem cell23_7037614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7037614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037614 prefixEnd_7037614 := by exact prefixLift 7037614
  have htrace : WordTrace (prefixWord ++ tailWord_7037614) baseStart_7037614 baseEnd_7037614 := by
    simpa [prefixWord, tailWord_7037614, baseEnd_7037614] using wordTrace_append hprefix tailTrace_7037614
  have hstable : (prefixWord ++ tailWord_7037614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037614).length < 2 ^ (prefixWord ++ tailWord_7037614).sum := by decide
  have hdescent : baseEnd_7037614 < baseStart_7037614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037630 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_7037630 : Nat := 118140960795 + 7037630 * 2 ^ 59
def prefixEnd_7037630 : Nat := 4983230072969 + 3 ^ 40 * 7037630 * 2
def baseEnd_7037630 : Nat := 3613686858501405473959535

theorem tailTrace_7037630 : CollatzResearch.WordTrace tailWord_7037630 prefixEnd_7037630 3613686858501405473959535 := by
  unfold tailWord_7037630
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085431686734489544806793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171122302329250610905636229 32085431686734489544806793)
  ·
    refine ⟨24064073765050867158605095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32085431686734489544806793 24064073765050867158605095)
    ·
      refine ⟨36096110647576300737907643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24064073765050867158605095 36096110647576300737907643)
      ·
        refine ⟨54144165971364451106861465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36096110647576300737907643 54144165971364451106861465)
        ·
          refine ⟨40608124478523338330146099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54144165971364451106861465 40608124478523338330146099)
          ·
            refine ⟨60912186717785007495219149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40608124478523338330146099 60912186717785007495219149)
            ·
              refine ⟨22842070019169377810707181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60912186717785007495219149 22842070019169377810707181)
              ·
                refine ⟨8565776257188516679015193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22842070019169377810707181 8565776257188516679015193)
                ·
                  refine ⟨6424332192891387509261395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8565776257188516679015193 6424332192891387509261395)
                  ·
                    refine ⟨9636498289337081263892093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424332192891387509261395 9636498289337081263892093)
                    ·
                      refine ⟨3613686858501405473959535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636498289337081263892093 3613686858501405473959535)
                      ·
                        rfl

theorem cell23_7037630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_7037630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037630 prefixEnd_7037630 := by exact prefixLift 7037630
  have htrace : WordTrace (prefixWord ++ tailWord_7037630) baseStart_7037630 baseEnd_7037630 := by
    simpa [prefixWord, tailWord_7037630, baseEnd_7037630] using wordTrace_append hprefix tailTrace_7037630
  have hstable : (prefixWord ++ tailWord_7037630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037630).length < 2 ^ (prefixWord ++ tailWord_7037630).sum := by decide
  have hdescent : baseEnd_7037630 < baseStart_7037630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037640 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_7037640 : Nat := 118140960795 + 7037640 * 2 ^ 59
def prefixEnd_7037640 : Nat := 4983230072969 + 3 ^ 40 * 7037640 * 2
def baseEnd_7037640 : Nat := 3613691993307950434834489

theorem tailTrace_7037640 : CollatzResearch.WordTrace tailWord_7037640 prefixEnd_7037640 3613691993307950434834489 := by
  unfold tailWord_7037640
  simp only [CollatzResearch.WordTrace]
  refine ⟨128341909111919844033159187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171122545482559792044212249 128341909111919844033159187)
  ·
    refine ⟨192512863667879766049738781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128341909111919844033159187 192512863667879766049738781)
    ·
      refine ⟨72192323875454912268652043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192512863667879766049738781 72192323875454912268652043)
      ·
        refine ⟨108288485813182368402978065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72192323875454912268652043 108288485813182368402978065)
        ·
          refine ⟨81216364359886776302233549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108288485813182368402978065 81216364359886776302233549)
          ·
            refine ⟨30456136634957541113337581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81216364359886776302233549 30456136634957541113337581)
            ·
              refine ⟨11421051238109077917501593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30456136634957541113337581 11421051238109077917501593)
              ·
                refine ⟨8565788428581808438126195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421051238109077917501593 8565788428581808438126195)
                ·
                  refine ⟨12848682642872712657189293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565788428581808438126195 12848682642872712657189293)
                  ·
                    refine ⟨4818255991077267246445985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12848682642872712657189293 4818255991077267246445985)
                    ·
                      refine ⟨3613691993307950434834489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818255991077267246445985 3613691993307950434834489)
                      ·
                        rfl

theorem cell23_7037640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_7037640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037640 prefixEnd_7037640 := by exact prefixLift 7037640
  have htrace : WordTrace (prefixWord ++ tailWord_7037640) baseStart_7037640 baseEnd_7037640 := by
    simpa [prefixWord, tailWord_7037640, baseEnd_7037640] using wordTrace_append hprefix tailTrace_7037640
  have hstable : (prefixWord ++ tailWord_7037640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037640).length < 2 ^ (prefixWord ++ tailWord_7037640).sum := by decide
  have hdescent : baseEnd_7037640 < baseStart_7037640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037656 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7037656 : Nat := 118140960795 + 7037656 * 2 ^ 59
def prefixEnd_7037656 : Nat := 4983230072969 + 3 ^ 40 * 7037656 * 2
def baseEnd_7037656 : Nat := 3613700208998422372234415

theorem tailTrace_7037656 : CollatzResearch.WordTrace tailWord_7037656 prefixEnd_7037656 3613700208998422372234415 := by
  unfold tailWord_7037656
  simp only [CollatzResearch.WordTrace]
  refine ⟨128342200895890861399450411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171122934527854481865933881 128342200895890861399450411)
  ·
    refine ⟨192513301343836292099175617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128342200895890861399450411 192513301343836292099175617)
    ·
      refine ⟨144384976007877219074381713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192513301343836292099175617 144384976007877219074381713)
      ·
        refine ⟨108288732005907914305786285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144384976007877219074381713 108288732005907914305786285)
        ·
          refine ⟨40608274502215467864669857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108288732005907914305786285 40608274502215467864669857)
          ·
            refine ⟨30456205876661600898502393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40608274502215467864669857 30456205876661600898502393)
            ·
              refine ⟨22842154407496200673876795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30456205876661600898502393 22842154407496200673876795)
              ·
                refine ⟨34263231611244301010815193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22842154407496200673876795 34263231611244301010815193)
                ·
                  refine ⟨25697423708433225758111395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34263231611244301010815193 25697423708433225758111395)
                  ·
                    refine ⟨38546135562649838637167093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25697423708433225758111395 38546135562649838637167093)
                    ·
                      refine ⟨3613700208998422372234415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38546135562649838637167093 3613700208998422372234415)
                      ·
                        rfl

theorem cell23_7037656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7037656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037656 prefixEnd_7037656 := by exact prefixLift 7037656
  have htrace : WordTrace (prefixWord ++ tailWord_7037656) baseStart_7037656 baseEnd_7037656 := by
    simpa [prefixWord, tailWord_7037656, baseEnd_7037656] using wordTrace_append hprefix tailTrace_7037656
  have hstable : (prefixWord ++ tailWord_7037656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037656).length < 2 ^ (prefixWord ++ tailWord_7037656).sum := by decide
  have hdescent : baseEnd_7037656 < baseStart_7037656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037706 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_7037706 : Nat := 118140960795 + 7037706 * 2 ^ 59
def prefixEnd_7037706 : Nat := 4983230072969 + 3 ^ 40 * 7037706 * 2
def baseEnd_7037706 : Nat := 1204575294343715725536395

theorem tailTrace_7037706 : CollatzResearch.WordTrace tailWord_7037706 prefixEnd_7037706 1204575294343715725536395 := by
  unfold tailWord_7037706
  simp only [CollatzResearch.WordTrace]
  refine ⟨64171556360400145334555243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171124150294400387558813981 64171556360400145334555243)
  ·
    refine ⟨96257334540600218001832865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64171556360400145334555243 96257334540600218001832865)
    ·
      refine ⟨72193000905450163501374649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96257334540600218001832865 72193000905450163501374649)
      ·
        refine ⟨54144750679087622626030987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72193000905450163501374649 54144750679087622626030987)
        ·
          refine ⟨81217126018631433939046481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54144750679087622626030987 81217126018631433939046481)
          ·
            refine ⟨60912844513973575454284861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81217126018631433939046481 60912844513973575454284861)
            ·
              refine ⟨22842316692740090795356823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60912844513973575454284861 22842316692740090795356823)
              ·
                refine ⟨34263475039110136193035235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22842316692740090795356823 34263475039110136193035235)
                ·
                  refine ⟨51395212558665204289552853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34263475039110136193035235 51395212558665204289552853)
                  ·
                    refine ⟨1204575294343715725536395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51395212558665204289552853 1204575294343715725536395)
                    ·
                      rfl

theorem cell23_7037706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_7037706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037706 prefixEnd_7037706 := by exact prefixLift 7037706
  have htrace : WordTrace (prefixWord ++ tailWord_7037706) baseStart_7037706 baseEnd_7037706 := by
    simpa [prefixWord, tailWord_7037706, baseEnd_7037706] using wordTrace_append hprefix tailTrace_7037706
  have hstable : (prefixWord ++ tailWord_7037706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037706).length < 2 ^ (prefixWord ++ tailWord_7037706).sum := by decide
  have hdescent : baseEnd_7037706 < baseStart_7037706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037756 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_7037756 : Nat := 118140960795 + 7037756 * 2 ^ 59
def prefixEnd_7037756 : Nat := 4983230072969 + 3 ^ 40 * 7037756 * 2
def baseEnd_7037756 : Nat := 3613751557063871980983955

theorem tailTrace_7037756 : CollatzResearch.WordTrace tailWord_7037756 prefixEnd_7037756 3613751557063871980983955 := by
  unfold tailWord_7037756
  simp only [CollatzResearch.WordTrace]
  refine ⟨128344024545709719938770561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171125366060946293251694081 128344024545709719938770561)
  ·
    refine ⟨96258018409282289954077921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128344024545709719938770561 96258018409282289954077921)
    ·
      refine ⟨72193513806961717465558441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96258018409282289954077921 72193513806961717465558441)
      ·
        refine ⟨54145135355221288099168831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72193513806961717465558441 54145135355221288099168831)
        ·
          refine ⟨81217703032831932148753247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54145135355221288099168831 81217703032831932148753247)
          ·
            refine ⟨121826554549247898223129871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81217703032831932148753247 121826554549247898223129871)
            ·
              refine ⟨182739831823871847334694807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121826554549247898223129871 182739831823871847334694807)
              ·
                refine ⟨274109747735807771002042211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182739831823871847334694807 274109747735807771002042211)
                ·
                  refine ⟨411164621603711656503063317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274109747735807771002042211 411164621603711656503063317)
                  ·
                    refine ⟨19273341637673983898581093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 411164621603711656503063317 19273341637673983898581093)
                    ·
                      refine ⟨3613751557063871980983955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19273341637673983898581093 3613751557063871980983955)
                      ·
                        rfl

theorem cell23_7037756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_7037756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037756 prefixEnd_7037756 := by exact prefixLift 7037756
  have htrace : WordTrace (prefixWord ++ tailWord_7037756) baseStart_7037756 baseEnd_7037756 := by
    simpa [prefixWord, tailWord_7037756, baseEnd_7037756] using wordTrace_append hprefix tailTrace_7037756
  have hstable : (prefixWord ++ tailWord_7037756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037756).length < 2 ^ (prefixWord ++ tailWord_7037756).sum := by decide
  have hdescent : baseEnd_7037756 < baseStart_7037756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037763 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3]
def baseStart_7037763 : Nat := 118140960795 + 7037763 * 2 ^ 59
def prefixEnd_7037763 : Nat := 4983230072969 + 3 ^ 40 * 7037763 * 2
def baseEnd_7037763 : Nat := 3613755151428453453596423

theorem tailTrace_7037763 : CollatzResearch.WordTrace tailWord_7037763 prefixEnd_7037763 3613755151428453453596423 := by
  unfold tailWord_7037763
  simp only [CollatzResearch.WordTrace]
  refine ⟨256688304402394080073045943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171125536268262720048697295 256688304402394080073045943)
  ·
    refine ⟨385032456603591120109568915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256688304402394080073045943 385032456603591120109568915)
    ·
      refine ⟨577548684905386680164353373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385032456603591120109568915 577548684905386680164353373)
      ·
        refine ⟨216580756839520005061632515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577548684905386680164353373 216580756839520005061632515)
        ·
          refine ⟨324871135259280007592448773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216580756839520005061632515 324871135259280007592448773)
          ·
            refine ⟨60913337861115001423584145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324871135259280007592448773 60913337861115001423584145)
            ·
              refine ⟨45685003395836251067688109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60913337861115001423584145 45685003395836251067688109)
              ·
                refine ⟨17131876273438594150383041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45685003395836251067688109 17131876273438594150383041)
                ·
                  refine ⟨12848907205078945612787281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17131876273438594150383041 12848907205078945612787281)
                  ·
                    refine ⟨9636680403809209209590461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12848907205078945612787281 9636680403809209209590461)
                    ·
                      refine ⟨3613755151428453453596423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636680403809209209590461 3613755151428453453596423)
                      ·
                        rfl

theorem cell23_7037763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_7037763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037763 prefixEnd_7037763 := by exact prefixLift 7037763
  have htrace : WordTrace (prefixWord ++ tailWord_7037763) baseStart_7037763 baseEnd_7037763 := by
    simpa [prefixWord, tailWord_7037763, baseEnd_7037763] using wordTrace_append hprefix tailTrace_7037763
  have hstable : (prefixWord ++ tailWord_7037763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037763).length < 2 ^ (prefixWord ++ tailWord_7037763).sum := by decide
  have hdescent : baseEnd_7037763 < baseStart_7037763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037770 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_7037770 : Nat := 118140960795 + 7037770 * 2 ^ 59
def prefixEnd_7037770 : Nat := 4983230072969 + 3 ^ 40 * 7037770 * 2
def baseEnd_7037770 : Nat := 1204586248597678308736297

theorem tailTrace_7037770 : CollatzResearch.WordTrace tailWord_7037770 prefixEnd_7037770 1204586248597678308736297 := by
  unfold tailWord_7037770
  simp only [CollatzResearch.WordTrace]
  refine ⟨64172139928342180067137691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171125706475579146845700509 64172139928342180067137691)
  ·
    refine ⟨96258209892513270100706537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64172139928342180067137691 96258209892513270100706537)
    ·
      refine ⟨72193657419384952575529903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96258209892513270100706537 72193657419384952575529903)
      ·
        refine ⟨108290486129077428863294855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72193657419384952575529903 108290486129077428863294855)
        ·
          refine ⟨162435729193616143294942283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108290486129077428863294855 162435729193616143294942283)
          ·
            refine ⟨243653593790424214942413425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162435729193616143294942283 243653593790424214942413425)
            ·
              refine ⟨182740195342818161206810069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243653593790424214942413425 182740195342818161206810069)
              ·
                refine ⟨4282973328347300653284611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 182740195342818161206810069 4282973328347300653284611)
                ·
                  refine ⟨6424459992520950979926917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282973328347300653284611 6424459992520950979926917)
                  ·
                    refine ⟨1204586248597678308736297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424459992520950979926917 1204586248597678308736297)
                    ·
                      rfl

theorem cell23_7037770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_7037770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037770 prefixEnd_7037770 := by exact prefixLift 7037770
  have htrace : WordTrace (prefixWord ++ tailWord_7037770) baseStart_7037770 baseEnd_7037770 := by
    simpa [prefixWord, tailWord_7037770, baseEnd_7037770] using wordTrace_append hprefix tailTrace_7037770
  have hstable : (prefixWord ++ tailWord_7037770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037770).length < 2 ^ (prefixWord ++ tailWord_7037770).sum := by decide
  have hdescent : baseEnd_7037770 < baseStart_7037770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037800 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 6]
def baseStart_7037800 : Nat := 118140960795 + 7037800 * 2 ^ 59
def prefixEnd_7037800 : Nat := 4983230072969 + 3 ^ 40 * 7037800 * 2
def baseEnd_7037800 : Nat := 401530461134741089870417

theorem tailTrace_7037800 : CollatzResearch.WordTrace tailWord_7037800 prefixEnd_7037800 401530461134741089870417 := by
  unfold tailWord_7037800
  simp only [CollatzResearch.WordTrace]
  refine ⟨128344826951630017696071427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171126435935506690261428569 128344826951630017696071427)
  ·
    refine ⟨192517240427445026544107141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128344826951630017696071427 192517240427445026544107141)
    ·
      refine ⟨36096982580145942477020089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192517240427445026544107141 36096982580145942477020089)
      ·
        refine ⟨27072736935109456857765067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36096982580145942477020089 27072736935109456857765067)
        ·
          refine ⟨40609105402664185286647601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27072736935109456857765067 40609105402664185286647601)
          ·
            refine ⟨30456829051998138964985701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40609105402664185286647601 30456829051998138964985701)
            ·
              refine ⟨5710655447249651055934819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30456829051998138964985701 5710655447249651055934819)
              ·
                refine ⟨8565983170874476583902229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710655447249651055934819 8565983170874476583902229)
                ·
                  refine ⟨401530461134741089870417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8565983170874476583902229 401530461134741089870417)
                  ·
                    rfl

theorem cell23_7037800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 6].length) (baseStart_7037800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037800 prefixEnd_7037800 := by exact prefixLift 7037800
  have htrace : WordTrace (prefixWord ++ tailWord_7037800) baseStart_7037800 baseEnd_7037800 := by
    simpa [prefixWord, tailWord_7037800, baseEnd_7037800] using wordTrace_append hprefix tailTrace_7037800
  have hstable : (prefixWord ++ tailWord_7037800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037800).length < 2 ^ (prefixWord ++ tailWord_7037800).sum := by decide
  have hdescent : baseEnd_7037800 < baseStart_7037800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037803 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 5, 2]
def baseStart_7037803 : Nat := 118140960795 + 7037803 * 2 ^ 59
def prefixEnd_7037803 : Nat := 4983230072969 + 3 ^ 40 * 7037803 * 2
def baseEnd_7037803 : Nat := 3613775690654633297096239

theorem tailTrace_7037803 : CollatzResearch.WordTrace tailWord_7037803 prefixEnd_7037803 3613775690654633297096239 := by
  unfold tailWord_7037803
  simp only [CollatzResearch.WordTrace]
  refine ⟨256689763322249166904502063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171126508881499444603001375 256689763322249166904502063)
  ·
    refine ⟨385034644983373750356753095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256689763322249166904502063 385034644983373750356753095)
    ·
      refine ⟨577551967475060625535129643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385034644983373750356753095 577551967475060625535129643)
      ·
        refine ⟨866327951212590938302694465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577551967475060625535129643 866327951212590938302694465)
        ·
          refine ⟨649745963409443203727020849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866327951212590938302694465 649745963409443203727020849)
          ·
            refine ⟨487309472557082402795265637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649745963409443203727020849 487309472557082402795265637)
            ·
              refine ⟨91370526104452950524112307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487309472557082402795265637 91370526104452950524112307)
              ·
                refine ⟨137055789156679425786168461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91370526104452950524112307 137055789156679425786168461)
                ·
                  refine ⟨51395920933754784669813173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137055789156679425786168461 51395920933754784669813173)
                  ·
                    refine ⟨4818367587539511062794985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51395920933754784669813173 4818367587539511062794985)
                    ·
                      refine ⟨3613775690654633297096239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818367587539511062794985 3613775690654633297096239)
                      ·
                        rfl

theorem cell23_7037803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5, 2].length) (baseStart_7037803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037803 prefixEnd_7037803 := by exact prefixLift 7037803
  have htrace : WordTrace (prefixWord ++ tailWord_7037803) baseStart_7037803 baseEnd_7037803 := by
    simpa [prefixWord, tailWord_7037803, baseEnd_7037803] using wordTrace_append hprefix tailTrace_7037803
  have hstable : (prefixWord ++ tailWord_7037803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037803).length < 2 ^ (prefixWord ++ tailWord_7037803).sum := by decide
  have hdescent : baseEnd_7037803 < baseStart_7037803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037810 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7037810 : Nat := 118140960795 + 7037810 * 2 ^ 59
def prefixEnd_7037810 : Nat := 4983230072969 + 3 ^ 40 * 7037810 * 2
def baseEnd_7037810 : Nat := 3613779285019214769708707

theorem tailTrace_7037810 : CollatzResearch.WordTrace tailWord_7037810 prefixEnd_7037810 3613779285019214769708707 := by
  unfold tailWord_7037810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64172504658305951775001721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171126679088815871400004589 64172504658305951775001721)
  ·
    refine ⟨48129378493729463831251291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64172504658305951775001721 48129378493729463831251291)
    ·
      refine ⟨72194067740594195746876937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48129378493729463831251291 72194067740594195746876937)
      ·
        refine ⟨54145550805445646810157703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72194067740594195746876937 54145550805445646810157703)
        ·
          refine ⟨81218326208168470215236555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54145550805445646810157703 81218326208168470215236555)
          ·
            refine ⟨121827489312252705322854833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81218326208168470215236555 121827489312252705322854833)
            ·
              refine ⟨91370616984189528992141125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121827489312252705322854833 91370616984189528992141125)
              ·
                refine ⟨17131990684535536686026461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91370616984189528992141125 17131990684535536686026461)
                ·
                  refine ⟨6424496506700826257259923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131990684535536686026461 6424496506700826257259923)
                  ·
                    refine ⟨9636744760051239385889885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424496506700826257259923 9636744760051239385889885)
                    ·
                      refine ⟨3613779285019214769708707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636744760051239385889885 3613779285019214769708707)
                      ·
                        rfl

theorem cell23_7037810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7037810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037810 prefixEnd_7037810 := by exact prefixLift 7037810
  have htrace : WordTrace (prefixWord ++ tailWord_7037810) baseStart_7037810 baseEnd_7037810 := by
    simpa [prefixWord, tailWord_7037810, baseEnd_7037810] using wordTrace_append hprefix tailTrace_7037810
  have hstable : (prefixWord ++ tailWord_7037810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037810).length < 2 ^ (prefixWord ++ tailWord_7037810).sum := by decide
  have hdescent : baseEnd_7037810 < baseStart_7037810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037827 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 1, 1, 3]
def baseStart_7037827 : Nat := 118140960795 + 7037827 * 2 ^ 59
def prefixEnd_7037827 : Nat := 4983230072969 + 3 ^ 40 * 7037827 * 2
def baseEnd_7037827 : Nat := 3613788014190341203196129

theorem tailTrace_7037827 : CollatzResearch.WordTrace tailWord_7037827 prefixEnd_7037827 3613788014190341203196129 := by
  unfold tailWord_7037827
  simp only [CollatzResearch.WordTrace]
  refine ⟨256690638674162219003375735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171127092449441479335583823 256690638674162219003375735)
  ·
    refine ⟨385035958011243328505063603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256690638674162219003375735 385035958011243328505063603)
    ·
      refine ⟨577553937016864992757595405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385035958011243328505063603 577553937016864992757595405)
      ·
        refine ⟨216582726381324372284098277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577553937016864992757595405 216582726381324372284098277)
        ·
          refine ⟨40609261196498319803268427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216582726381324372284098277 40609261196498319803268427)
          ·
            refine ⟨60913891794747479704902641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40609261196498319803268427 60913891794747479704902641)
            ·
              refine ⟨45685418846060609778676981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60913891794747479704902641 45685418846060609778676981)
              ·
                refine ⟨4283008016818182166750967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45685418846060609778676981 4283008016818182166750967)
                ·
                  refine ⟨6424512025227273250126451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283008016818182166750967 6424512025227273250126451)
                  ·
                    refine ⟨9636768037840909875189677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424512025227273250126451 9636768037840909875189677)
                    ·
                      refine ⟨3613788014190341203196129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636768037840909875189677 3613788014190341203196129)
                      ·
                        rfl

theorem cell23_7037827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_7037827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037827 prefixEnd_7037827 := by exact prefixLift 7037827
  have htrace : WordTrace (prefixWord ++ tailWord_7037827) baseStart_7037827 baseEnd_7037827 := by
    simpa [prefixWord, tailWord_7037827, baseEnd_7037827] using wordTrace_append hprefix tailTrace_7037827
  have hstable : (prefixWord ++ tailWord_7037827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037827).length < 2 ^ (prefixWord ++ tailWord_7037827).sum := by decide
  have hdescent : baseEnd_7037827 < baseStart_7037827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037844 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7037844 : Nat := 118140960795 + 7037844 * 2 ^ 59
def prefixEnd_7037844 : Nat := 4983230072969 + 3 ^ 40 * 7037844 * 2
def baseEnd_7037844 : Nat := 3613796743361467636683551

theorem tailTrace_7037844 : CollatzResearch.WordTrace tailWord_7037844 prefixEnd_7037844 3613796743361467636683551 := by
  unfold tailWord_7037844
  simp only [CollatzResearch.WordTrace]
  refine ⟨128345629357550315453372293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171127505810067087271163057 128345629357550315453372293)
  ·
    refine ⟨24064805504540684147507305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128345629357550315453372293 24064805504540684147507305)
    ·
      refine ⟨18048604128405513110630479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24064805504540684147507305 18048604128405513110630479)
      ·
        refine ⟨27072906192608269665945719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18048604128405513110630479 27072906192608269665945719)
        ·
          refine ⟨40609359288912404498918579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27072906192608269665945719 40609359288912404498918579)
          ·
            refine ⟨60914038933368606748377869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40609359288912404498918579 60914038933368606748377869)
            ·
              refine ⟨22842764600013227530641701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60914038933368606748377869 22842764600013227530641701)
              ·
                refine ⟨4283018362502480161995319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22842764600013227530641701 4283018362502480161995319)
                ·
                  refine ⟨6424527543753720242992979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283018362502480161995319 6424527543753720242992979)
                  ·
                    refine ⟨9636791315630580364489469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424527543753720242992979 9636791315630580364489469)
                    ·
                      refine ⟨3613796743361467636683551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636791315630580364489469 3613796743361467636683551)
                      ·
                        rfl

theorem cell23_7037844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7037844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037844 prefixEnd_7037844 := by exact prefixLift 7037844
  have htrace : WordTrace (prefixWord ++ tailWord_7037844) baseStart_7037844 baseEnd_7037844 := by
    simpa [prefixWord, tailWord_7037844, baseEnd_7037844] using wordTrace_append hprefix tailTrace_7037844
  have hstable : (prefixWord ++ tailWord_7037844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037844).length < 2 ^ (prefixWord ++ tailWord_7037844).sum := by decide
  have hdescent : baseEnd_7037844 < baseStart_7037844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037853 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7037853 : Nat := 118140960795 + 7037853 * 2 ^ 59
def prefixEnd_7037853 : Nat := 4983230072969 + 3 ^ 40 * 7037853 * 2
def baseEnd_7037853 : Nat := 3613801364687358101471009

theorem tailTrace_7037853 : CollatzResearch.WordTrace tailWord_7037853 prefixEnd_7037853 3613801364687358101471009 := by
  unfold tailWord_7037853
  simp only [CollatzResearch.WordTrace]
  refine ⟨256691586972068025443822213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171127724648045350295881475 256691586972068025443822213)
  ·
    refine ⟨48129672557262754770716665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256691586972068025443822213 48129672557262754770716665)
    ·
      refine ⟨36097254417947066078037499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48129672557262754770716665 36097254417947066078037499)
      ·
        refine ⟨54145881626920599117056249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36097254417947066078037499 54145881626920599117056249)
        ·
          refine ⟨40609411220190449337792187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54145881626920599117056249 40609411220190449337792187)
          ·
            refine ⟨60914116830285674006688281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40609411220190449337792187 60914116830285674006688281)
            ·
              refine ⟨45685587622714255505016211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60914116830285674006688281 45685587622714255505016211)
              ·
                refine ⟨68528381434071383257524317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45685587622714255505016211 68528381434071383257524317)
                ·
                  refine ⟨25698143037776768721571619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68528381434071383257524317 25698143037776768721571619)
                  ·
                    refine ⟨38547214556665153082357429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25698143037776768721571619 38547214556665153082357429)
                    ·
                      refine ⟨3613801364687358101471009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38547214556665153082357429 3613801364687358101471009)
                      ·
                        rfl

theorem cell23_7037853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7037853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037853 prefixEnd_7037853 := by exact prefixLift 7037853
  have htrace : WordTrace (prefixWord ++ tailWord_7037853) baseStart_7037853 baseEnd_7037853 := by
    simpa [prefixWord, tailWord_7037853, baseEnd_7037853] using wordTrace_append hprefix tailTrace_7037853
  have hstable : (prefixWord ++ tailWord_7037853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037853).length < 2 ^ (prefixWord ++ tailWord_7037853).sum := by decide
  have hdescent : baseEnd_7037853 < baseStart_7037853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037860 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_7037860 : Nat := 118140960795 + 7037860 * 2 ^ 59
def prefixEnd_7037860 : Nat := 4983230072969 + 3 ^ 40 * 7037860 * 2
def baseEnd_7037860 : Nat := 1204601653017313191361159

theorem tailTrace_7037860 : CollatzResearch.WordTrace tailWord_7037860 prefixEnd_7037860 1204601653017313191361159 := by
  unfold tailWord_7037860
  simp only [CollatzResearch.WordTrace]
  refine ⟨128345921141521332819663517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171127894855361777092884689 128345921141521332819663517)
  ·
    refine ⟨48129720428070499807373819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128345921141521332819663517 48129720428070499807373819)
    ·
      refine ⟨72194580642105749711060729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48129720428070499807373819 72194580642105749711060729)
      ·
        refine ⟨54145935481579312283295547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72194580642105749711060729 54145935481579312283295547)
        ·
          refine ⟨81218903222368968424943321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54145935481579312283295547 81218903222368968424943321)
          ·
            refine ⟨60914177416776726318707491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81218903222368968424943321 60914177416776726318707491)
            ·
              refine ⟨91371266125165089478061237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60914177416776726318707491 91371266125165089478061237)
              ·
                refine ⟨8566056199234227138568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91371266125165089478061237 8566056199234227138568241)
                ·
                  refine ⟨6424542149425670353926181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566056199234227138568241 6424542149425670353926181)
                  ·
                    refine ⟨1204601653017313191361159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424542149425670353926181 1204601653017313191361159)
                    ·
                      rfl

theorem cell23_7037860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_7037860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037860 prefixEnd_7037860 := by exact prefixLift 7037860
  have htrace : WordTrace (prefixWord ++ tailWord_7037860) baseStart_7037860 baseEnd_7037860 := by
    simpa [prefixWord, tailWord_7037860, baseEnd_7037860] using wordTrace_append hprefix tailTrace_7037860
  have hstable : (prefixWord ++ tailWord_7037860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037860).length < 2 ^ (prefixWord ++ tailWord_7037860).sum := by decide
  have hdescent : baseEnd_7037860 < baseStart_7037860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037917 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_7037917 : Nat := 118140960795 + 7037917 * 2 ^ 59
def prefixEnd_7037917 : Nat := 4983230072969 + 3 ^ 40 * 7037917 * 2
def baseEnd_7037917 : Nat := 3613834227449245851070715

theorem tailTrace_7037917 : CollatzResearch.WordTrace tailWord_7037917 prefixEnd_7037917 3613834227449245851070715 := by
  unfold tailWord_7037917
  simp only [CollatzResearch.WordTrace]
  refine ⟨256693921243836164374152005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171129280829224109582768003 256693921243836164374152005)
  ·
    refine ⟨48130110233219280820153501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256693921243836164374152005 48130110233219280820153501)
    ·
      refine ⟨18048791337457230307557563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48130110233219280820153501 18048791337457230307557563)
      ·
        refine ⟨27073187006185845461336345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18048791337457230307557563 27073187006185845461336345)
        ·
          refine ⟨20304890254639384096002259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27073187006185845461336345 20304890254639384096002259)
          ·
            refine ⟨30457335381959076144003389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20304890254639384096002259 30457335381959076144003389)
            ·
              refine ⟨11421500768234653554001271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30457335381959076144003389 11421500768234653554001271)
              ·
                refine ⟨17132251152351980331001907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421500768234653554001271 17132251152351980331001907)
                ·
                  refine ⟨25698376728527970496502861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17132251152351980331001907 25698376728527970496502861)
                  ·
                    refine ⟨9636891273197988936188573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25698376728527970496502861 9636891273197988936188573)
                    ·
                      refine ⟨3613834227449245851070715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9636891273197988936188573 3613834227449245851070715)
                      ·
                        rfl

theorem cell23_7037917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_7037917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037917 prefixEnd_7037917 := by exact prefixLift 7037917
  have htrace : WordTrace (prefixWord ++ tailWord_7037917) baseStart_7037917 baseEnd_7037917 := by
    simpa [prefixWord, tailWord_7037917, baseEnd_7037917] using wordTrace_append hprefix tailTrace_7037917
  have hstable : (prefixWord ++ tailWord_7037917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037917).length < 2 ^ (prefixWord ++ tailWord_7037917).sum := by decide
  have hdescent : baseEnd_7037917 < baseStart_7037917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7037957 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_7037957 : Nat := 118140960795 + 7037957 * 2 ^ 59
def prefixEnd_7037957 : Nat := 4983230072969 + 3 ^ 40 * 7037957 * 2
def baseEnd_7037957 : Nat := 3613854766675425694570531

theorem tailTrace_7037957 : CollatzResearch.WordTrace tailWord_7037957 prefixEnd_7037957 3613854766675425694570531 := by
  unfold tailWord_7037957
  simp only [CollatzResearch.WordTrace]
  refine ⟨256695380163691251205608125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171130253442460834137072083 256695380163691251205608125)
  ·
    refine ⟨96260767561384219202103047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256695380163691251205608125 96260767561384219202103047)
    ·
      refine ⟨144391151342076328803154571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96260767561384219202103047 144391151342076328803154571)
      ·
        refine ⟨216586727013114493204731857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144391151342076328803154571 216586727013114493204731857)
        ·
          refine ⟨162440045259835869903548893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216586727013114493204731857 162440045259835869903548893)
          ·
            refine ⟨60915016972438451213830835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162440045259835869903548893 60915016972438451213830835)
            ·
              refine ⟨91372525458657676820746253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60915016972438451213830835 91372525458657676820746253)
              ·
                refine ⟨34264697046996628807779845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91372525458657676820746253 34264697046996628807779845)
                ·
                  refine ⟨6424630696311867901458721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34264697046996628807779845 6424630696311867901458721)
                  ·
                    refine ⟨4818473022233900926094041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424630696311867901458721 4818473022233900926094041)
                    ·
                      refine ⟨3613854766675425694570531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818473022233900926094041 3613854766675425694570531)
                      ·
                        rfl

theorem cell23_7037957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_7037957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7037957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7037957 prefixEnd_7037957 := by exact prefixLift 7037957
  have htrace : WordTrace (prefixWord ++ tailWord_7037957) baseStart_7037957 baseEnd_7037957 := by
    simpa [prefixWord, tailWord_7037957, baseEnd_7037957] using wordTrace_append hprefix tailTrace_7037957
  have hstable : (prefixWord ++ tailWord_7037957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7037957).length < 2 ^ (prefixWord ++ tailWord_7037957).sum := by decide
  have hdescent : baseEnd_7037957 < baseStart_7037957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7037957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038010 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_7038010 : Nat := 118140960795 + 7038010 * 2 ^ 59
def prefixEnd_7038010 : Nat := 4983230072969 + 3 ^ 40 * 7038010 * 2
def baseEnd_7038010 : Nat := 1204627327050037995735929

theorem tailTrace_7038010 : CollatzResearch.WordTrace tailWord_7038010 prefixEnd_7038010 1204627327050037995735929 := by
  unfold tailWord_7038010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64174328308124810314321871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171131542154999494171524989 64174328308124810314321871)
  ·
    refine ⟨96261492462187215471482807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64174328308124810314321871 96261492462187215471482807)
    ·
      refine ⟨144392238693280823207224211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96261492462187215471482807 144392238693280823207224211)
      ·
        refine ⟨216588358039921234810836317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144392238693280823207224211 216588358039921234810836317)
        ·
          refine ⟨81220634264970463054063619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216588358039921234810836317 81220634264970463054063619)
          ·
            refine ⟨121830951397455694581095429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81220634264970463054063619 121830951397455694581095429)
            ·
              refine ⟨22843303387022942733955393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121830951397455694581095429 22843303387022942733955393)
              ·
                refine ⟨17132477540267207050466545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22843303387022942733955393 17132477540267207050466545)
                ·
                  refine ⟨12849358155200405287849909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17132477540267207050466545 12849358155200405287849909)
                  ·
                    refine ⟨1204627327050037995735929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12849358155200405287849909 1204627327050037995735929)
                    ·
                      rfl

theorem cell23_7038010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_7038010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038010 prefixEnd_7038010 := by exact prefixLift 7038010
  have htrace : WordTrace (prefixWord ++ tailWord_7038010) baseStart_7038010 baseEnd_7038010 := by
    simpa [prefixWord, tailWord_7038010, baseEnd_7038010] using wordTrace_append hprefix tailTrace_7038010
  have hstable : (prefixWord ++ tailWord_7038010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038010).length < 2 ^ (prefixWord ++ tailWord_7038010).sum := by decide
  have hdescent : baseEnd_7038010 < baseStart_7038010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038014 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_7038014 : Nat := 118140960795 + 7038014 * 2 ^ 59
def prefixEnd_7038014 : Nat := 4983230072969 + 3 ^ 40 * 7038014 * 2
def baseEnd_7038014 : Nat := 401542670563636885728641

theorem tailTrace_7038014 : CollatzResearch.WordTrace tailWord_7038014 prefixEnd_7038014 401542670563636885728641 := by
  unfold tailWord_7038014
  simp only [CollatzResearch.WordTrace]
  refine ⟨32087182390560593742554137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171131639416323166626955397 32087182390560593742554137)
  ·
    refine ⟨24065386792920445306915603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32087182390560593742554137 24065386792920445306915603)
    ·
      refine ⟨36098080189380667960373405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24065386792920445306915603 36098080189380667960373405)
      ·
        refine ⟨13536780071017750485140027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36098080189380667960373405 13536780071017750485140027)
        ·
          refine ⟨20305170106526625727710041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536780071017750485140027 20305170106526625727710041)
          ·
            refine ⟨15228877579894969295782531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20305170106526625727710041 15228877579894969295782531)
            ·
              refine ⟨22843316369842453943673797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15228877579894969295782531 22843316369842453943673797)
              ·
                refine ⟨4283121819345460114438837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22843316369842453943673797 4283121819345460114438837)
                ·
                  refine ⟨401542670563636885728641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283121819345460114438837 401542670563636885728641)
                  ·
                    rfl

theorem cell23_7038014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_7038014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038014 prefixEnd_7038014 := by exact prefixLift 7038014
  have htrace : WordTrace (prefixWord ++ tailWord_7038014) baseStart_7038014 baseEnd_7038014 := by
    simpa [prefixWord, tailWord_7038014, baseEnd_7038014] using wordTrace_append hprefix tailTrace_7038014
  have hstable : (prefixWord ++ tailWord_7038014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038014).length < 2 ^ (prefixWord ++ tailWord_7038014).sum := by decide
  have hdescent : baseEnd_7038014 < baseStart_7038014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038030 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_7038030 : Nat := 118140960795 + 7038030 * 2 ^ 59
def prefixEnd_7038030 : Nat := 4983230072969 + 3 ^ 40 * 7038030 * 2
def baseEnd_7038030 : Nat := 3613892250763203908957695

theorem tailTrace_7038030 : CollatzResearch.WordTrace tailWord_7038030 prefixEnd_7038030 3613892250763203908957695 := by
  unfold tailWord_7038030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32087255336553348084126943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171132028461617856448677029 32087255336553348084126943)
  ·
    refine ⟨48130883004830022126190415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32087255336553348084126943 48130883004830022126190415)
    ·
      refine ⟨72196324507245033189285623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48130883004830022126190415 72196324507245033189285623)
      ·
        refine ⟨108294486760867549783928435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72196324507245033189285623 108294486760867549783928435)
        ·
          refine ⟨162441730141301324675892653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108294486760867549783928435 162441730141301324675892653)
          ·
            refine ⟨60915648802987996753459745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162441730141301324675892653 60915648802987996753459745)
            ·
              refine ⟨45686736602240997565094809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60915648802987996753459745 45686736602240997565094809)
              ·
                refine ⟨34265052451680748173821107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45686736602240997565094809 34265052451680748173821107)
                ·
                  refine ⟨51397578677521122260731661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34265052451680748173821107 51397578677521122260731661)
                  ·
                    refine ⟨19274092004070420847774373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51397578677521122260731661 19274092004070420847774373)
                    ·
                      refine ⟨3613892250763203908957695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19274092004070420847774373 3613892250763203908957695)
                      ·
                        rfl

theorem cell23_7038030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_7038030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038030 prefixEnd_7038030 := by exact prefixLift 7038030
  have htrace : WordTrace (prefixWord ++ tailWord_7038030) baseStart_7038030 baseEnd_7038030 := by
    simpa [prefixWord, tailWord_7038030, baseEnd_7038030] using wordTrace_append hprefix tailTrace_7038030
  have hstable : (prefixWord ++ tailWord_7038030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038030).length < 2 ^ (prefixWord ++ tailWord_7038030).sum := by decide
  have hdescent : baseEnd_7038030 < baseStart_7038030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038090 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7038090 : Nat := 118140960795 + 7038090 * 2 ^ 59
def prefixEnd_7038090 : Nat := 4983230072969 + 3 ^ 40 * 7038090 * 2
def baseEnd_7038090 : Nat := 3613923059602473674207419

theorem tailTrace_7038090 : CollatzResearch.WordTrace tailWord_7038090 prefixEnd_7038090 3613923059602473674207419 := by
  unfold tailWord_7038090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64175057768052353730049931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171133487381472943280133149 64175057768052353730049931)
  ·
    refine ⟨96262586652078530595074897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64175057768052353730049931 96262586652078530595074897)
    ·
      refine ⟨72196939989058897946306173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96262586652078530595074897 72196939989058897946306173)
      ·
        refine ⟨27073852495897086729864815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72196939989058897946306173 27073852495897086729864815)
        ·
          refine ⟨40610778743845630094797223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27073852495897086729864815 40610778743845630094797223)
          ·
            refine ⟨60916168115768445142195835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40610778743845630094797223 60916168115768445142195835)
            ·
              refine ⟨91374252173652667713293753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60916168115768445142195835 91374252173652667713293753)
              ·
                refine ⟨68530689130239500784970315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91374252173652667713293753 68530689130239500784970315)
                ·
                  refine ⟨102796033695359251177455473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68530689130239500784970315 102796033695359251177455473)
                  ·
                    refine ⟨77097025271519438383091605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102796033695359251177455473 77097025271519438383091605)
                    ·
                      refine ⟨3613923059602473674207419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77097025271519438383091605 3613923059602473674207419)
                      ·
                        rfl

theorem cell23_7038090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7038090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038090 prefixEnd_7038090 := by exact prefixLift 7038090
  have htrace : WordTrace (prefixWord ++ tailWord_7038090) baseStart_7038090 baseEnd_7038090 := by
    simpa [prefixWord, tailWord_7038090, baseEnd_7038090] using wordTrace_append hprefix tailTrace_7038090
  have hstable : (prefixWord ++ tailWord_7038090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038090).length < 2 ^ (prefixWord ++ tailWord_7038090).sum := by decide
  have hdescent : baseEnd_7038090 < baseStart_7038090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038117 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_7038117 : Nat := 118140960795 + 7038117 * 2 ^ 59
def prefixEnd_7038117 : Nat := 4983230072969 + 3 ^ 40 * 7038117 * 2
def baseEnd_7038117 : Nat := 1204645641193381689523265

theorem tailTrace_7038117 : CollatzResearch.WordTrace tailWord_7038117 prefixEnd_7038117 1204645641193381689523265 := by
  unfold tailWord_7038117
  simp only [CollatzResearch.WordTrace]
  refine ⟨256701215843111598531432605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171134143895407732354288403 256701215843111598531432605)
  ·
    refine ⟨96262955941166849449287227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256701215843111598531432605 96262955941166849449287227)
    ·
      refine ⟨144394433911750274173930841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96262955941166849449287227 144394433911750274173930841)
      ·
        refine ⟨108295825433812705630448131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144394433911750274173930841 108295825433812705630448131)
        ·
          refine ⟨162443738150719058445672197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108295825433812705630448131 162443738150719058445672197)
          ·
            refine ⟨30458200903259823458563537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162443738150719058445672197 30458200903259823458563537)
            ·
              refine ⟨22843650677444867593922653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30458200903259823458563537 22843650677444867593922653)
              ·
                refine ⟨8566369004041825347720995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22843650677444867593922653 8566369004041825347720995)
                ·
                  refine ⟨12849553506062738021581493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8566369004041825347720995 12849553506062738021581493)
                  ·
                    refine ⟨1204645641193381689523265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12849553506062738021581493 1204645641193381689523265)
                    ·
                      rfl

theorem cell23_7038117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_7038117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038117 prefixEnd_7038117 := by exact prefixLift 7038117
  have htrace : WordTrace (prefixWord ++ tailWord_7038117) baseStart_7038117 baseEnd_7038117 := by
    simpa [prefixWord, tailWord_7038117, baseEnd_7038117] using wordTrace_append hprefix tailTrace_7038117
  have hstable : (prefixWord ++ tailWord_7038117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038117).length < 2 ^ (prefixWord ++ tailWord_7038117).sum := by decide
  have hdescent : baseEnd_7038117 < baseStart_7038117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038154 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_7038154 : Nat := 118140960795 + 7038154 * 2 ^ 59
def prefixEnd_7038154 : Nat := 4983230072969 + 3 ^ 40 * 7038154 * 2
def baseEnd_7038154 : Nat := 3613955922364361423807125

theorem tailTrace_7038154 : CollatzResearch.WordTrace tailWord_7038154 prefixEnd_7038154 3613955922364361423807125 := by
  unfold tailWord_7038154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64175641335994388462632379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171135043562651702567019677 64175641335994388462632379)
  ·
    refine ⟨96263462003991582693948569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64175641335994388462632379 96263462003991582693948569)
    ·
      refine ⟨72197596502993687020461427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96263462003991582693948569 72197596502993687020461427)
      ·
        refine ⟨108296394754490530530692141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72197596502993687020461427 108296394754490530530692141)
        ·
          refine ⟨40611148032933948949009553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108296394754490530530692141 40611148032933948949009553)
          ·
            refine ⟨30458361024700461711757165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40611148032933948949009553 30458361024700461711757165)
            ·
              refine ⟨11421885384262673141908937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30458361024700461711757165 11421885384262673141908937)
              ·
                refine ⟨8566414038197004856431703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421885384262673141908937 8566414038197004856431703)
                ·
                  refine ⟨12849621057295507284647555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8566414038197004856431703 12849621057295507284647555)
                  ·
                    refine ⟨19274431585943260926971333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12849621057295507284647555 19274431585943260926971333)
                    ·
                      refine ⟨3613955922364361423807125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19274431585943260926971333 3613955922364361423807125)
                      ·
                        rfl

theorem cell23_7038154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_7038154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038154 prefixEnd_7038154 := by exact prefixLift 7038154
  have htrace : WordTrace (prefixWord ++ tailWord_7038154) baseStart_7038154 baseEnd_7038154 := by
    simpa [prefixWord, tailWord_7038154, baseEnd_7038154] using wordTrace_append hprefix tailTrace_7038154
  have hstable : (prefixWord ++ tailWord_7038154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038154).length < 2 ^ (prefixWord ++ tailWord_7038154).sum := by decide
  have hdescent : baseEnd_7038154 < baseStart_7038154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038181 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_7038181 : Nat := 118140960795 + 7038181 * 2 ^ 59
def prefixEnd_7038181 : Nat := 4983230072969 + 3 ^ 40 * 7038181 * 2
def baseEnd_7038181 : Nat := 1204656595447344272723167

theorem tailTrace_7038181 : CollatzResearch.WordTrace tailWord_7038181 prefixEnd_7038181 1204656595447344272723167 := by
  unfold tailWord_7038181
  simp only [CollatzResearch.WordTrace]
  refine ⟨256703550114879737461762397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171135700076586491641174931 256703550114879737461762397)
  ·
    refine ⟨96263831293079901548160899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256703550114879737461762397 96263831293079901548160899)
    ·
      refine ⟨144395746939619852322241349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96263831293079901548160899 144395746939619852322241349)
      ·
        refine ⟨27074202551178722310420253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144395746939619852322241349 27074202551178722310420253)
        ·
          refine ⟨10152825956692020866407595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27074202551178722310420253 10152825956692020866407595)
          ·
            refine ⟨15229238935038031299611393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10152825956692020866407595 15229238935038031299611393)
            ·
              refine ⟨11421929201278523474708545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15229238935038031299611393 11421929201278523474708545)
              ·
                refine ⟨8566446900958892606031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421929201278523474708545 8566446900958892606031409)
                ·
                  refine ⟨6424835175719169454523557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566446900958892606031409 6424835175719169454523557)
                  ·
                    refine ⟨1204656595447344272723167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424835175719169454523557 1204656595447344272723167)
                    ·
                      rfl

theorem cell23_7038181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_7038181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038181 prefixEnd_7038181 := by exact prefixLift 7038181
  have htrace : WordTrace (prefixWord ++ tailWord_7038181) baseStart_7038181 baseEnd_7038181 := by
    simpa [prefixWord, tailWord_7038181, baseEnd_7038181] using wordTrace_append hprefix tailTrace_7038181
  have hstable : (prefixWord ++ tailWord_7038181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038181).length < 2 ^ (prefixWord ++ tailWord_7038181).sum := by decide
  have hdescent : baseEnd_7038181 < baseStart_7038181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038188 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 1, 2, 2]
def baseStart_7038188 : Nat := 118140960795 + 7038188 * 2 ^ 59
def prefixEnd_7038188 : Nat := 4983230072969 + 3 ^ 40 * 7038188 * 2
def baseEnd_7038188 : Nat := 3613973380706614290781969

theorem tailTrace_7038188 : CollatzResearch.WordTrace tailWord_7038188 prefixEnd_7038188 3613973380706614290781969 := by
  unfold tailWord_7038188
  simp only [CollatzResearch.WordTrace]
  refine ⟨128351902712927188828633609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171135870283902918438178145 128351902712927188828633609)
  ·
    refine ⟨96263927034695391621475207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128351902712927188828633609 96263927034695391621475207)
    ·
      refine ⟨144395890552043087432212811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96263927034695391621475207 144395890552043087432212811)
      ·
        refine ⟨216593835828064631148319217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144395890552043087432212811 216593835828064631148319217)
        ·
          refine ⟨162445376871048473361239413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216593835828064631148319217 162445376871048473361239413)
          ·
            refine ⟨15229254081660794377616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162445376871048473361239413 15229254081660794377616195)
            ·
              refine ⟨22843881122491191566424293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15229254081660794377616195 22843881122491191566424293)
              ·
                refine ⟨4283227710467098418704555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22843881122491191566424293 4283227710467098418704555)
                ·
                  refine ⟨6424841565700647628056833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283227710467098418704555 6424841565700647628056833)
                  ·
                    refine ⟨4818631174275485721042625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424841565700647628056833 4818631174275485721042625)
                    ·
                      refine ⟨3613973380706614290781969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818631174275485721042625 3613973380706614290781969)
                      ·
                        rfl

theorem cell23_7038188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_7038188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038188 prefixEnd_7038188 := by exact prefixLift 7038188
  have htrace : WordTrace (prefixWord ++ tailWord_7038188) baseStart_7038188 baseEnd_7038188 := by
    simpa [prefixWord, tailWord_7038188, baseEnd_7038188] using wordTrace_append hprefix tailTrace_7038188
  have hstable : (prefixWord ++ tailWord_7038188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038188).length < 2 ^ (prefixWord ++ tailWord_7038188).sum := by decide
  have hdescent : baseEnd_7038188 < baseStart_7038188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038194 : List Nat := [3, 2, 1, 3, 3, 2, 1, 8]
def baseStart_7038194 : Nat := 118140960795 + 7038194 * 2 ^ 59
def prefixEnd_7038194 : Nat := 4983230072969 + 3 ^ 40 * 7038194 * 2
def baseEnd_7038194 : Nat := 133850980058908935826183

theorem tailTrace_7038194 : CollatzResearch.WordTrace tailWord_7038194 prefixEnd_7038194 133850980058908935826183 := by
  unfold tailWord_7038194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64176006065958160170496409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171136016175888427121323757 64176006065958160170496409)
  ·
    refine ⟨48132004549468620127872307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64176006065958160170496409 48132004549468620127872307)
    ·
      refine ⟨72198006824202930191808461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48132004549468620127872307 72198006824202930191808461)
      ·
        refine ⟨27074252559076098821928173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72198006824202930191808461 27074252559076098821928173)
        ·
          refine ⟨10152844709653537058223065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27074252559076098821928173 10152844709653537058223065)
          ·
            refine ⟨7614633532240152793667299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10152844709653537058223065 7614633532240152793667299)
            ·
              refine ⟨11421950298360229190500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614633532240152793667299 11421950298360229190500949)
              ·
                refine ⟨133850980058908935826183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11421950298360229190500949 133850980058908935826183)
                ·
                  rfl

theorem cell23_7038194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_7038194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038194 prefixEnd_7038194 := by exact prefixLift 7038194
  have htrace : WordTrace (prefixWord ++ tailWord_7038194) baseStart_7038194 baseEnd_7038194 := by
    simpa [prefixWord, tailWord_7038194, baseEnd_7038194] using wordTrace_append hprefix tailTrace_7038194
  have hstable : (prefixWord ++ tailWord_7038194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038194).length < 2 ^ (prefixWord ++ tailWord_7038194).sum := by decide
  have hdescent : baseEnd_7038194 < baseStart_7038194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038200 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7038200 : Nat := 118140960795 + 7038200 * 2 ^ 59
def prefixEnd_7038200 : Nat := 4983230072969 + 3 ^ 40 * 7038200 * 2
def baseEnd_7038200 : Nat := 3613979542474468243831913

theorem tailTrace_7038200 : CollatzResearch.WordTrace tailWord_7038200 prefixEnd_7038200 3613979542474468243831913 := by
  unfold tailWord_7038200
  simp only [CollatzResearch.WordTrace]
  refine ⟨128352121550905451853352027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171136162067873935804469369 128352121550905451853352027)
  ·
    refine ⟨192528182326358177780028041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128352121550905451853352027 192528182326358177780028041)
    ·
      refine ⟨144396136744768633335021031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192528182326358177780028041 144396136744768633335021031)
      ·
        refine ⟨216594205117152950002531547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144396136744768633335021031 216594205117152950002531547)
        ·
          refine ⟨324891307675729425003797321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216594205117152950002531547 324891307675729425003797321)
          ·
            refine ⟨243668480756797068752847991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324891307675729425003797321 243668480756797068752847991)
            ·
              refine ⟨365502721135195603129271987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243668480756797068752847991 365502721135195603129271987)
              ·
                refine ⟨548254081702793404693907981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365502721135195603129271987 548254081702793404693907981)
                ·
                  refine ⟨205595280638547526760215493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548254081702793404693907981 205595280638547526760215493)
                  ·
                    refine ⟨38549115119727661267540405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205595280638547526760215493 38549115119727661267540405)
                    ·
                      refine ⟨3613979542474468243831913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38549115119727661267540405 3613979542474468243831913)
                      ·
                        rfl

theorem cell23_7038200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7038200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038200 prefixEnd_7038200 := by exact prefixLift 7038200
  have htrace : WordTrace (prefixWord ++ tailWord_7038200) baseStart_7038200 baseEnd_7038200 := by
    simpa [prefixWord, tailWord_7038200, baseEnd_7038200] using wordTrace_append hprefix tailTrace_7038200
  have hstable : (prefixWord ++ tailWord_7038200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038200).length < 2 ^ (prefixWord ++ tailWord_7038200).sum := by decide
  have hdescent : baseEnd_7038200 < baseStart_7038200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038231 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7038231 : Nat := 118140960795 + 7038231 * 2 ^ 59
def prefixEnd_7038231 : Nat := 4983230072969 + 3 ^ 40 * 7038231 * 2
def baseEnd_7038231 : Nat := 3613995460374757622544271

theorem tailTrace_7038231 : CollatzResearch.WordTrace tailWord_7038231 prefixEnd_7038231 3613995460374757622544271 := by
  unfold tailWord_7038231
  simp only [CollatzResearch.WordTrace]
  refine ⟨256705373764698596001082547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171136915843132397334055031 256705373764698596001082547)
  ·
    refine ⟨385058060647047894001623821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256705373764698596001082547 385058060647047894001623821)
    ·
      refine ⟨144396772742642960250608933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 385058060647047894001623821 144396772742642960250608933)
      ·
        refine ⟨27074394889245555046989175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144396772742642960250608933 27074394889245555046989175)
        ·
          refine ⟨40611592333868332570483763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27074394889245555046989175 40611592333868332570483763)
          ·
            refine ⟨60917388500802498855725645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40611592333868332570483763 60917388500802498855725645)
            ·
              refine ⟨22844020687800937070897117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60917388500802498855725645 22844020687800937070897117)
              ·
                refine ⟨8566507757925351401586419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22844020687800937070897117 8566507757925351401586419)
                ·
                  refine ⟨12849761636888027102379629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8566507757925351401586419 12849761636888027102379629)
                  ·
                    refine ⟨4818660613833010163392361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12849761636888027102379629 4818660613833010163392361)
                    ·
                      refine ⟨3613995460374757622544271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818660613833010163392361 3613995460374757622544271)
                      ·
                        rfl

theorem cell23_7038231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7038231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038231 prefixEnd_7038231 := by exact prefixLift 7038231
  have htrace : WordTrace (prefixWord ++ tailWord_7038231) baseStart_7038231 baseEnd_7038231 := by
    simpa [prefixWord, tailWord_7038231, baseEnd_7038231] using wordTrace_append hprefix tailTrace_7038231
  have hstable : (prefixWord ++ tailWord_7038231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038231).length < 2 ^ (prefixWord ++ tailWord_7038231).sum := by decide
  have hdescent : baseEnd_7038231 < baseStart_7038231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038261 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_7038261 : Nat := 118140960795 + 7038261 * 2 ^ 59
def prefixEnd_7038261 : Nat := 4983230072969 + 3 ^ 40 * 7038261 * 2
def baseEnd_7038261 : Nat := 3614010864794392505169133

theorem tailTrace_7038261 : CollatzResearch.WordTrace tailWord_7038261 prefixEnd_7038261 3614010864794392505169133 := by
  unfold tailWord_7038261
  simp only [CollatzResearch.WordTrace]
  refine ⟨256706467954589911124674637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171137645303059940749783091 256706467954589911124674637)
  ·
    refine ⟨96264925482971216671752989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256706467954589911124674637 96264925482971216671752989)
    ·
      refine ⟨36099347056114206251907371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96264925482971216671752989 36099347056114206251907371)
      ·
        refine ⟨54149020584171309377861057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36099347056114206251907371 54149020584171309377861057)
        ·
          refine ⟨40611765438128482033395793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54149020584171309377861057 40611765438128482033395793)
          ·
            refine ⟨30458824078596361525046845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40611765438128482033395793 30458824078596361525046845)
            ·
              refine ⟨11422059029473635571892567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30458824078596361525046845 11422059029473635571892567)
              ·
                refine ⟨17133088544210453357838851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11422059029473635571892567 17133088544210453357838851)
                ·
                  refine ⟨25699632816315680036758277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17133088544210453357838851 25699632816315680036758277)
                  ·
                    refine ⟨4818681153059190006892177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25699632816315680036758277 4818681153059190006892177)
                    ·
                      refine ⟨3614010864794392505169133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818681153059190006892177 3614010864794392505169133)
                      ·
                        rfl

theorem cell23_7038261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_7038261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038261 prefixEnd_7038261 := by exact prefixLift 7038261
  have htrace : WordTrace (prefixWord ++ tailWord_7038261) baseStart_7038261 baseEnd_7038261 := by
    simpa [prefixWord, tailWord_7038261, baseEnd_7038261] using wordTrace_append hprefix tailTrace_7038261
  have hstable : (prefixWord ++ tailWord_7038261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038261).length < 2 ^ (prefixWord ++ tailWord_7038261).sum := by decide
  have hdescent : baseEnd_7038261 < baseStart_7038261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038277 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_7038277 : Nat := 118140960795 + 7038277 * 2 ^ 59
def prefixEnd_7038277 : Nat := 4983230072969 + 3 ^ 40 * 7038277 * 2
def baseEnd_7038277 : Nat := 3614019080484864442569059

theorem tailTrace_7038277 : CollatzResearch.WordTrace tailWord_7038277 prefixEnd_7038277 3614019080484864442569059 := by
  unfold tailWord_7038277
  simp only [CollatzResearch.WordTrace]
  refine ⟨256707051522531945857257085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171138034348354630571504723 256707051522531945857257085)
  ·
    refine ⟨96265144320949479696471407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256707051522531945857257085 96265144320949479696471407)
    ·
      refine ⟨144397716481424219544707111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96265144320949479696471407 144397716481424219544707111)
      ·
        refine ⟨216596574722136329317060667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144397716481424219544707111 216596574722136329317060667)
        ·
          refine ⟨324894862083204493975591001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216596574722136329317060667 324894862083204493975591001)
          ·
            refine ⟨243671146562403370481693251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324894862083204493975591001 243671146562403370481693251)
            ·
              refine ⟨365506719843605055722539877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243671146562403370481693251 365506719843605055722539877)
              ·
                refine ⟨68532509970675947947976227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365506719843605055722539877 68532509970675947947976227)
                ·
                  refine ⟨102798764956013921921964341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68532509970675947947976227 102798764956013921921964341)
                  ·
                    refine ⟨9637384214626305180184157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102798764956013921921964341 9637384214626305180184157)
                    ·
                      refine ⟨3614019080484864442569059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9637384214626305180184157 3614019080484864442569059)
                      ·
                        rfl

theorem cell23_7038277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_7038277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038277 prefixEnd_7038277 := by exact prefixLift 7038277
  have htrace : WordTrace (prefixWord ++ tailWord_7038277) baseStart_7038277 baseEnd_7038277 := by
    simpa [prefixWord, tailWord_7038277, baseEnd_7038277] using wordTrace_append hprefix tailTrace_7038277
  have hstable : (prefixWord ++ tailWord_7038277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038277).length < 2 ^ (prefixWord ++ tailWord_7038277).sum := by decide
  have hdescent : baseEnd_7038277 < baseStart_7038277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038297 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_7038297 : Nat := 118140960795 + 7038297 * 2 ^ 59
def prefixEnd_7038297 : Nat := 4983230072969 + 3 ^ 40 * 7038297 * 2
def baseEnd_7038297 : Nat := 1204676450032651454772989

theorem tailTrace_7038297 : CollatzResearch.WordTrace tailWord_7038297 prefixEnd_7038297 1204676450032651454772989 := by
  unfold tailWord_7038297
  simp only [CollatzResearch.WordTrace]
  refine ⟨256707780982459489272985145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171138520654972992848656763 256707780982459489272985145)
  ·
    refine ⟨192530835736844616954738859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256707780982459489272985145 192530835736844616954738859)
    ·
      refine ⟨288796253605266925432108289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192530835736844616954738859 288796253605266925432108289)
      ·
        refine ⟨216597190203950194074081217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288796253605266925432108289 216597190203950194074081217)
        ·
          refine ⟨162447892652962645555560913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216597190203950194074081217 162447892652962645555560913)
          ·
            refine ⟨121835919489721984166670685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162447892652962645555560913 121835919489721984166670685)
            ·
              refine ⟨45688469808645744062501507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121835919489721984166670685 45688469808645744062501507)
              ·
                refine ⟨68532704712968616093752261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45688469808645744062501507 68532704712968616093752261)
                ·
                  refine ⟨12849882133681615517578549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68532704712968616093752261 12849882133681615517578549)
                  ·
                    refine ⟨1204676450032651454772989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12849882133681615517578549 1204676450032651454772989)
                    ·
                      rfl

theorem cell23_7038297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_7038297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038297 prefixEnd_7038297 := by exact prefixLift 7038297
  have htrace : WordTrace (prefixWord ++ tailWord_7038297) baseStart_7038297 baseEnd_7038297 := by
    simpa [prefixWord, tailWord_7038297, baseEnd_7038297] using wordTrace_append hprefix tailTrace_7038297
  have hstable : (prefixWord ++ tailWord_7038297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038297).length < 2 ^ (prefixWord ++ tailWord_7038297).sum := by decide
  have hdescent : baseEnd_7038297 < baseStart_7038297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038307 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_7038307 : Nat := 118140960795 + 7038307 * 2 ^ 59
def prefixEnd_7038307 : Nat := 4983230072969 + 3 ^ 40 * 7038307 * 2
def baseEnd_7038307 : Nat := 3614034484904499325193921

theorem tailTrace_7038307 : CollatzResearch.WordTrace tailWord_7038307 prefixEnd_7038307 3614034484904499325193921 := by
  unfold tailWord_7038307
  simp only [CollatzResearch.WordTrace]
  refine ⟨256708145712423260980849175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171138763808282173987232783 256708145712423260980849175)
  ·
    refine ⟨385062218568634891471273763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256708145712423260980849175 385062218568634891471273763)
    ·
      refine ⟨577593327852952337206910645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385062218568634891471273763 577593327852952337206910645)
      ·
        refine ⟨54149374486214281613147873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 577593327852952337206910645 54149374486214281613147873)
        ·
          refine ⟨40612030864660711209860905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54149374486214281613147873 40612030864660711209860905)
          ·
            refine ⟨30459023148495533407395679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40612030864660711209860905 30459023148495533407395679)
            ·
              refine ⟨45688534722743300111093519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30459023148495533407395679 45688534722743300111093519)
              ·
                refine ⟨68532802084114950166640279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45688534722743300111093519 68532802084114950166640279)
                ·
                  refine ⟨102799203126172425249960419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68532802084114950166640279 102799203126172425249960419)
                  ·
                    refine ⟨154198804689258637874940629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102799203126172425249960419 154198804689258637874940629)
                    ·
                      refine ⟨3614034484904499325193921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154198804689258637874940629 3614034484904499325193921)
                      ·
                        rfl

theorem cell23_7038307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_7038307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038307 prefixEnd_7038307 := by exact prefixLift 7038307
  have htrace : WordTrace (prefixWord ++ tailWord_7038307) baseStart_7038307 baseEnd_7038307 := by
    simpa [prefixWord, tailWord_7038307, baseEnd_7038307] using wordTrace_append hprefix tailTrace_7038307
  have hstable : (prefixWord ++ tailWord_7038307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038307).length < 2 ^ (prefixWord ++ tailWord_7038307).sum := by decide
  have hdescent : baseEnd_7038307 < baseStart_7038307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038312 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7038312 : Nat := 118140960795 + 7038312 * 2 ^ 59
def prefixEnd_7038312 : Nat := 4983230072969 + 3 ^ 40 * 7038312 * 2
def baseEnd_7038312 : Nat := 3614037052307771805631399

theorem tailTrace_7038312 : CollatzResearch.WordTrace tailWord_7038312 prefixEnd_7038312 3614037052307771805631399 := by
  unfold tailWord_7038312
  simp only [CollatzResearch.WordTrace]
  refine ⟨128354164038702573417390595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171138885384936764556520793 128354164038702573417390595)
  ·
    refine ⟨192531246058053860126085893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128354164038702573417390595 192531246058053860126085893)
    ·
      refine ⟨36099608635885098773641105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192531246058053860126085893 36099608635885098773641105)
      ·
        refine ⟨27074706476913824080230829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36099608635885098773641105 27074706476913824080230829)
        ·
          refine ⟨10153014928842684030086561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27074706476913824080230829 10153014928842684030086561)
          ·
            refine ⟨7614761196632013022564921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10153014928842684030086561 7614761196632013022564921)
            ·
              refine ⟨5711070897474009766923691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614761196632013022564921 5711070897474009766923691)
              ·
                refine ⟨8566606346211014650385537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711070897474009766923691 8566606346211014650385537)
                ·
                  refine ⟨6424954759658260987789153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566606346211014650385537 6424954759658260987789153)
                  ·
                    refine ⟨4818716069743695740841865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424954759658260987789153 4818716069743695740841865)
                    ·
                      refine ⟨3614037052307771805631399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4818716069743695740841865 3614037052307771805631399)
                      ·
                        rfl

theorem cell23_7038312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7038312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038312 prefixEnd_7038312 := by exact prefixLift 7038312
  have htrace : WordTrace (prefixWord ++ tailWord_7038312) baseStart_7038312 baseEnd_7038312 := by
    simpa [prefixWord, tailWord_7038312, baseEnd_7038312] using wordTrace_append hprefix tailTrace_7038312
  have hstable : (prefixWord ++ tailWord_7038312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038312).length < 2 ^ (prefixWord ++ tailWord_7038312).sum := by decide
  have hdescent : baseEnd_7038312 < baseStart_7038312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038347 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_7038347 : Nat := 118140960795 + 7038347 * 2 ^ 59
def prefixEnd_7038347 : Nat := 4983230072969 + 3 ^ 40 * 7038347 * 2
def baseEnd_7038347 : Nat := 3614055024130679168693737

theorem tailTrace_7038347 : CollatzResearch.WordTrace tailWord_7038347 prefixEnd_7038347 3614055024130679168693737 := by
  unfold tailWord_7038347
  simp only [CollatzResearch.WordTrace]
  refine ⟨256709604632278347812305295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171139736421518898541536863 256709604632278347812305295)
  ·
    refine ⟨385064406948417521718457943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256709604632278347812305295 385064406948417521718457943)
    ·
      refine ⟨577596610422626282577686915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385064406948417521718457943 577596610422626282577686915)
      ·
        refine ⟨866394915633939423866530373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577596610422626282577686915 866394915633939423866530373)
        ·
          refine ⟨162449046681363641974974445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 866394915633939423866530373 162449046681363641974974445)
          ·
            refine ⟨60918392505511365740615417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162449046681363641974974445 60918392505511365740615417)
            ·
              refine ⟨45688794379133524305461563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60918392505511365740615417 45688794379133524305461563)
              ·
                refine ⟨68533191568700286458192345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45688794379133524305461563 68533191568700286458192345)
                ·
                  refine ⟨51399893676525214843644259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68533191568700286458192345 51399893676525214843644259)
                  ·
                    refine ⟨77099840514787822265466389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51399893676525214843644259 77099840514787822265466389)
                    ·
                      refine ⟨3614055024130679168693737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77099840514787822265466389 3614055024130679168693737)
                      ·
                        rfl

theorem cell23_7038347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_7038347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038347 prefixEnd_7038347 := by exact prefixLift 7038347
  have htrace : WordTrace (prefixWord ++ tailWord_7038347) baseStart_7038347 baseEnd_7038347 := by
    simpa [prefixWord, tailWord_7038347, baseEnd_7038347] using wordTrace_append hprefix tailTrace_7038347
  have hstable : (prefixWord ++ tailWord_7038347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038347).length < 2 ^ (prefixWord ++ tailWord_7038347).sum := by decide
  have hdescent : baseEnd_7038347 < baseStart_7038347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7038357 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 8]
def baseStart_7038357 : Nat := 118140960795 + 7038357 * 2 ^ 59
def prefixEnd_7038357 : Nat := 4983230072969 + 3 ^ 40 * 7038357 * 2
def baseEnd_7038357 : Nat := 401562239881913792174299

theorem tailTrace_7038357 : CollatzResearch.WordTrace tailWord_7038357 prefixEnd_7038357 401562239881913792174299 := by
  unfold tailWord_7038357
  simp only [CollatzResearch.WordTrace]
  refine ⟨256709969362242119520169325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171139979574828079680112883 256709969362242119520169325)
  ·
    refine ⟨96266238510840794820063497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256709969362242119520169325 96266238510840794820063497)
    ·
      refine ⟨72199678883130596115047623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96266238510840794820063497 72199678883130596115047623)
      ·
        refine ⟨108299518324695894172571435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72199678883130596115047623 108299518324695894172571435)
        ·
          refine ⟨162449277487043841258857153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108299518324695894172571435 162449277487043841258857153)
          ·
            refine ⟨121836958115282880944142865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162449277487043841258857153 121836958115282880944142865)
            ·
              refine ⟨91377718586462160708107149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121836958115282880944142865 91377718586462160708107149)
              ·
                refine ⟨34266644469923310265540181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91377718586462160708107149 34266644469923310265540181)
                ·
                  refine ⟨401562239881913792174299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34266644469923310265540181 401562239881913792174299)
                  ·
                    rfl

theorem cell23_7038357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_7038357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7038357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7038357 prefixEnd_7038357 := by exact prefixLift 7038357
  have htrace : WordTrace (prefixWord ++ tailWord_7038357) baseStart_7038357 baseEnd_7038357 := by
    simpa [prefixWord, tailWord_7038357, baseEnd_7038357] using wordTrace_append hprefix tailTrace_7038357
  have hstable : (prefixWord ++ tailWord_7038357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7038357).length < 2 ^ (prefixWord ++ tailWord_7038357).sum := by decide
  have hdescent : baseEnd_7038357 < baseStart_7038357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7038357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
