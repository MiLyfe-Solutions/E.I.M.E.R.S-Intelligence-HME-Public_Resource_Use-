import V185TrunkScan23Chunk0289

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1714609 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1714609 : Nat := 118140960795 + 1714609 * 2 ^ 59
def prefixEnd_1714609 : Nat := 4983230072969 + 3 ^ 40 * 1714609 * 2
def baseEnd_1714609 : Nat := 880418551524987318102163

theorem tailTrace_1714609 : CollatzResearch.WordTrace tailWord_1714609 prefixEnd_1714609 880418551524987318102163 := by
  unfold tailWord_1714609
  simp only [CollatzResearch.WordTrace]
  refine ⟨62536927845271899748770881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41691285230181266499180587 62536927845271899748770881)
  ·
    refine ⟨46902695883953924811578161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62536927845271899748770881 46902695883953924811578161)
    ·
      refine ⟨35177021912965443608683621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46902695883953924811578161 35177021912965443608683621)
      ·
        refine ⟨6595691608681020676628179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35177021912965443608683621 6595691608681020676628179)
        ·
          refine ⟨9893537413021531014942269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595691608681020676628179 9893537413021531014942269)
          ·
            refine ⟨3710076529883074130603351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9893537413021531014942269 3710076529883074130603351)
            ·
              refine ⟨5565114794824611195905027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710076529883074130603351 5565114794824611195905027)
              ·
                refine ⟨8347672192236916793857541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565114794824611195905027 8347672192236916793857541)
                ·
                  refine ⟨1565188536044421898848289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8347672192236916793857541 1565188536044421898848289)
                  ·
                    refine ⟨1173891402033316424136217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565188536044421898848289 1173891402033316424136217)
                    ·
                      refine ⟨880418551524987318102163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173891402033316424136217 880418551524987318102163)
                      ·
                        rfl

theorem cell23_1714609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1714609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714609 prefixEnd_1714609 := by exact prefixLift 1714609
  have htrace : WordTrace (prefixWord ++ tailWord_1714609) baseStart_1714609 baseEnd_1714609 := by
    simpa [prefixWord, tailWord_1714609, baseEnd_1714609] using wordTrace_append hprefix tailTrace_1714609
  have hstable : (prefixWord ++ tailWord_1714609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714609).length < 2 ^ (prefixWord ++ tailWord_1714609).sum := by decide
  have hdescent : baseEnd_1714609 < baseStart_1714609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714615 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 7]
def baseStart_1714615 : Nat := 118140960795 + 1714615 * 2 ^ 59
def prefixEnd_1714615 : Nat := 4983230072969 + 3 ^ 40 * 1714615 * 2
def baseEnd_1714615 : Nat := 97824625823212699403015

theorem tailTrace_1714615 : CollatzResearch.WordTrace tailWord_1714615 prefixEnd_1714615 97824625823212699403015 := by
  unfold tailWord_1714615
  simp only [CollatzResearch.WordTrace]
  refine ⟨62537146683250162773489299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41691431122166775182326199 62537146683250162773489299)
  ·
    refine ⟨93805720024875244160233949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62537146683250162773489299 93805720024875244160233949)
    ·
      refine ⟨35177145009328216560087731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93805720024875244160233949 35177145009328216560087731)
      ·
        refine ⟨52765717513992324840131597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35177145009328216560087731 52765717513992324840131597)
        ·
          refine ⟨19787144067747121815049349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52765717513992324840131597 19787144067747121815049349)
          ·
            refine ⟨3710089512702585340321753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19787144067747121815049349 3710089512702585340321753)
            ·
              refine ⟨2782567134526939005241315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710089512702585340321753 2782567134526939005241315)
              ·
                refine ⟨4173850701790408507861973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782567134526939005241315 4173850701790408507861973)
                ·
                  refine ⟨97824625823212699403015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4173850701790408507861973 97824625823212699403015)
                  ·
                    rfl

theorem cell23_1714615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 7].length) (baseStart_1714615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714615 prefixEnd_1714615 := by exact prefixLift 1714615
  have htrace : WordTrace (prefixWord ++ tailWord_1714615) baseStart_1714615 baseEnd_1714615 := by
    simpa [prefixWord, tailWord_1714615, baseEnd_1714615] using wordTrace_append hprefix tailTrace_1714615
  have hstable : (prefixWord ++ tailWord_1714615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714615).length < 2 ^ (prefixWord ++ tailWord_1714615).sum := by decide
  have hdescent : baseEnd_1714615 < baseStart_1714615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714645 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1714645 : Nat := 118140960795 + 1714645 * 2 ^ 59
def prefixEnd_1714645 : Nat := 4983230072969 + 3 ^ 40 * 1714645 * 2
def baseEnd_1714645 : Nat := 293479012276183059083999

theorem tailTrace_1714645 : CollatzResearch.WordTrace tailWord_1714645 prefixEnd_1714645 293479012276183059083999 := by
  unfold tailWord_1714645
  simp only [CollatzResearch.WordTrace]
  refine ⟨62538240873141477897081389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41692160582094318598054259 62538240873141477897081389)
  ·
    refine ⟨23451840327428054211405521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62538240873141477897081389 23451840327428054211405521)
    ·
      refine ⟨17588880245571040658554141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23451840327428054211405521 17588880245571040658554141)
      ·
        refine ⟨6595830092089140246957803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17588880245571040658554141 6595830092089140246957803)
        ·
          refine ⟨9893745138133710370436705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595830092089140246957803 9893745138133710370436705)
          ·
            refine ⟨7420308853600282777827529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893745138133710370436705 7420308853600282777827529)
            ·
              refine ⟨5565231640200212083370647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420308853600282777827529 5565231640200212083370647)
              ·
                refine ⟨8347847460300318125055971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565231640200212083370647 8347847460300318125055971)
                ·
                  refine ⟨12521771190450477187583957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347847460300318125055971 12521771190450477187583957)
                  ·
                    refine ⟨293479012276183059083999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12521771190450477187583957 293479012276183059083999)
                    ·
                      rfl

theorem cell23_1714645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1714645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714645 prefixEnd_1714645 := by exact prefixLift 1714645
  have htrace : WordTrace (prefixWord ++ tailWord_1714645) baseStart_1714645 baseEnd_1714645 := by
    simpa [prefixWord, tailWord_1714645, baseEnd_1714645] using wordTrace_append hprefix tailTrace_1714645
  have hstable : (prefixWord ++ tailWord_1714645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714645).length < 2 ^ (prefixWord ++ tailWord_1714645).sum := by decide
  have hdescent : baseEnd_1714645 < baseStart_1714645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714677 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1714677 : Nat := 118140960795 + 1714677 * 2 ^ 59
def prefixEnd_1714677 : Nat := 4983230072969 + 3 ^ 40 * 1714677 * 2
def baseEnd_1714677 : Nat := 880453468209493052051851

theorem tailTrace_1714677 : CollatzResearch.WordTrace tailWord_1714677 prefixEnd_1714677 880453468209493052051851 := by
  unfold tailWord_1714677
  simp only [CollatzResearch.WordTrace]
  refine ⟨62539408009025547362246285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41692938672683698241497523 62539408009025547362246285)
  ·
    refine ⟨23452278003384580260842357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62539408009025547362246285 23452278003384580260842357)
    ·
      refine ⟨2198651062817304399453971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23452278003384580260842357 2198651062817304399453971)
      ·
        refine ⟨3297976594225956599180957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198651062817304399453971 3297976594225956599180957)
        ·
          refine ⟨1236741222834733724692859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3297976594225956599180957 1236741222834733724692859)
          ·
            refine ⟨1855111834252100587039289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236741222834733724692859 1855111834252100587039289)
            ·
              refine ⟨1391333875689075440279467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855111834252100587039289 1391333875689075440279467)
              ·
                refine ⟨2087000813533613160419201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391333875689075440279467 2087000813533613160419201)
                ·
                  refine ⟨1565250610150209870314401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087000813533613160419201 1565250610150209870314401)
                  ·
                    refine ⟨1173937957612657402735801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565250610150209870314401 1173937957612657402735801)
                    ·
                      refine ⟨880453468209493052051851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173937957612657402735801 880453468209493052051851)
                      ·
                        rfl

theorem cell23_1714677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1714677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714677 prefixEnd_1714677 := by exact prefixLift 1714677
  have htrace : WordTrace (prefixWord ++ tailWord_1714677) baseStart_1714677 baseEnd_1714677 := by
    simpa [prefixWord, tailWord_1714677, baseEnd_1714677] using wordTrace_append hprefix tailTrace_1714677
  have hstable : (prefixWord ++ tailWord_1714677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714677).length < 2 ^ (prefixWord ++ tailWord_1714677).sum := by decide
  have hdescent : baseEnd_1714677 < baseStart_1714677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714709 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_1714709 : Nat := 118140960795 + 1714709 * 2 ^ 59
def prefixEnd_1714709 : Nat := 4983230072969 + 3 ^ 40 * 1714709 * 2
def baseEnd_1714709 : Nat := 293489966530145642283901

theorem tailTrace_1714709 : CollatzResearch.WordTrace tailWord_1714709 prefixEnd_1714709 293489966530145642283901 := by
  unfold tailWord_1714709
  simp only [CollatzResearch.WordTrace]
  refine ⟨62540575144909616827411181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41693716763273077884940787 62540575144909616827411181)
  ·
    refine ⟨23452715679341106310279193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62540575144909616827411181 23452715679341106310279193)
    ·
      refine ⟨17589536759505829732709395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23452715679341106310279193 17589536759505829732709395)
      ·
        refine ⟨26384305139258744599064093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17589536759505829732709395 26384305139258744599064093)
        ·
          refine ⟨9894114427222029224649035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26384305139258744599064093 9894114427222029224649035)
          ·
            refine ⟨14841171640833043836973553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894114427222029224649035 14841171640833043836973553)
            ·
              refine ⟨11130878730624782877730165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14841171640833043836973553 11130878730624782877730165)
              ·
                refine ⟨1043519880996073394787203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11130878730624782877730165 1043519880996073394787203)
                ·
                  refine ⟨1565279821494110092180805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043519880996073394787203 1565279821494110092180805)
                  ·
                    refine ⟨293489966530145642283901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565279821494110092180805 293489966530145642283901)
                    ·
                      rfl

theorem cell23_1714709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_1714709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714709 prefixEnd_1714709 := by exact prefixLift 1714709
  have htrace : WordTrace (prefixWord ++ tailWord_1714709) baseStart_1714709 baseEnd_1714709 := by
    simpa [prefixWord, tailWord_1714709, baseEnd_1714709] using wordTrace_append hprefix tailTrace_1714709
  have hstable : (prefixWord ++ tailWord_1714709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714709).length < 2 ^ (prefixWord ++ tailWord_1714709).sum := by decide
  have hdescent : baseEnd_1714709 < baseStart_1714709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714732 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_1714732 : Nat := 118140960795 + 1714732 * 2 ^ 59
def prefixEnd_1714732 : Nat := 4983230072969 + 3 ^ 40 * 1714732 * 2
def baseEnd_1714732 : Nat := 880481709645490336864097

theorem tailTrace_1714732 : CollatzResearch.WordTrace tailWord_1714732 prefixEnd_1714732 880481709645490336864097 := by
  unfold tailWord_1714732
  simp only [CollatzResearch.WordTrace]
  refine ⟨31270707011913145877749225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41694276015884194503665633 31270707011913145877749225)
  ·
    refine ⟨23453030258934859408311919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31270707011913145877749225 23453030258934859408311919)
    ·
      refine ⟨35179545388402289112467879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23453030258934859408311919 35179545388402289112467879)
      ·
        refine ⟨52769318082603433668701819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35179545388402289112467879 52769318082603433668701819)
        ·
          refine ⟨79153977123905150503052729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52769318082603433668701819 79153977123905150503052729)
          ·
            refine ⟨59365482842928862877289547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79153977123905150503052729 59365482842928862877289547)
            ·
              refine ⟨89048224264393294315934321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59365482842928862877289547 89048224264393294315934321)
              ·
                refine ⟨66786168198294970736950741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89048224264393294315934321 66786168198294970736950741)
                ·
                  refine ⟨1565300817147538376647283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66786168198294970736950741 1565300817147538376647283)
                  ·
                    refine ⟨2347951225721307564970925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565300817147538376647283 2347951225721307564970925)
                    ·
                      refine ⟨880481709645490336864097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347951225721307564970925 880481709645490336864097)
                      ·
                        rfl

theorem cell23_1714732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_1714732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714732 prefixEnd_1714732 := by exact prefixLift 1714732
  have htrace : WordTrace (prefixWord ++ tailWord_1714732) baseStart_1714732 baseEnd_1714732 := by
    simpa [prefixWord, tailWord_1714732, baseEnd_1714732] using wordTrace_append hprefix tailTrace_1714732
  have hstable : (prefixWord ++ tailWord_1714732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714732).length < 2 ^ (prefixWord ++ tailWord_1714732).sum := by decide
  have hdescent : baseEnd_1714732 < baseStart_1714732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714745 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1714745 : Nat := 118140960795 + 1714745 * 2 ^ 59
def prefixEnd_1714745 : Nat := 4983230072969 + 3 ^ 40 * 1714745 * 2
def baseEnd_1714745 : Nat := 880488384893998786001537

theorem tailTrace_1714745 : CollatzResearch.WordTrace tailWord_1714745 prefixEnd_1714745 880488384893998786001537 := by
  unfold tailWord_1714745
  simp only [CollatzResearch.WordTrace]
  refine ⟨62541888172779194975721689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694592115186129983814459 62541888172779194975721689)
  ·
    refine ⟨46906416129584396231791267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62541888172779194975721689 46906416129584396231791267)
    ·
      refine ⟨70359624194376594347686901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46906416129584396231791267 70359624194376594347686901)
      ·
        refine ⟨6596214768222805720095647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70359624194376594347686901 6596214768222805720095647)
        ·
          refine ⟨9894322152334208580143471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596214768222805720095647 9894322152334208580143471)
          ·
            refine ⟨14841483228501312870215207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894322152334208580143471 14841483228501312870215207)
            ·
              refine ⟨22262224842751969305322811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841483228501312870215207 22262224842751969305322811)
              ·
                refine ⟨33393337264127953957984217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22262224842751969305322811 33393337264127953957984217)
                ·
                  refine ⟨25045002948095965468488163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33393337264127953957984217 25045002948095965468488163)
                  ·
                    refine ⟨37567504422143948202732245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25045002948095965468488163 37567504422143948202732245)
                    ·
                      refine ⟨880488384893998786001537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37567504422143948202732245 880488384893998786001537)
                      ·
                        rfl

theorem cell23_1714745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1714745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714745 prefixEnd_1714745 := by exact prefixLift 1714745
  have htrace : WordTrace (prefixWord ++ tailWord_1714745) baseStart_1714745 baseEnd_1714745 := by
    simpa [prefixWord, tailWord_1714745, baseEnd_1714745] using wordTrace_append hprefix tailTrace_1714745
  have hstable : (prefixWord ++ tailWord_1714745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714745).length < 2 ^ (prefixWord ++ tailWord_1714745).sum := by decide
  have hdescent : baseEnd_1714745 < baseStart_1714745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714749 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1714749 : Nat := 118140960795 + 1714749 * 2 ^ 59
def prefixEnd_1714749 : Nat := 4983230072969 + 3 ^ 40 * 1714749 * 2
def baseEnd_1714749 : Nat := 880490438816616770351519

theorem tailTrace_1714749 : CollatzResearch.WordTrace tailWord_1714749 prefixEnd_1714749 880490438816616770351519 := by
  unfold tailWord_1714749
  simp only [CollatzResearch.WordTrace]
  refine ⟨62542034064764703658867301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694689376509802439244867 62542034064764703658867301)
  ·
    refine ⟨11726631387143381936037619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62542034064764703658867301 11726631387143381936037619)
    ·
      refine ⟨17589947080715072904056429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726631387143381936037619 17589947080715072904056429)
      ·
        refine ⟨6596230155268152339021161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17589947080715072904056429 6596230155268152339021161)
        ·
          refine ⟨4947172616451114254265871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596230155268152339021161 4947172616451114254265871)
          ·
            refine ⟨7420758924676671381398807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947172616451114254265871 7420758924676671381398807)
            ·
              refine ⟨11131138387015007072098211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420758924676671381398807 11131138387015007072098211)
              ·
                refine ⟨16696707580522510608147317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131138387015007072098211 16696707580522510608147317)
                ·
                  refine ⟨1565316335673985369513811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16696707580522510608147317 1565316335673985369513811)
                  ·
                    refine ⟨2347974503510978054270717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565316335673985369513811 2347974503510978054270717)
                    ·
                      refine ⟨880490438816616770351519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347974503510978054270717 880490438816616770351519)
                      ·
                        rfl

theorem cell23_1714749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1714749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714749 prefixEnd_1714749 := by exact prefixLift 1714749
  have htrace : WordTrace (prefixWord ++ tailWord_1714749) baseStart_1714749 baseEnd_1714749 := by
    simpa [prefixWord, tailWord_1714749, baseEnd_1714749] using wordTrace_append hprefix tailTrace_1714749
  have hstable : (prefixWord ++ tailWord_1714749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714749).length < 2 ^ (prefixWord ++ tailWord_1714749).sum := by decide
  have hdescent : baseEnd_1714749 < baseStart_1714749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714759 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_1714759 : Nat := 118140960795 + 1714759 * 2 ^ 59
def prefixEnd_1714759 : Nat := 4983230072969 + 3 ^ 40 * 1714759 * 2
def baseEnd_1714759 : Nat := 880495573623161731226473

theorem tailTrace_1714759 : CollatzResearch.WordTrace tailWord_1714759 prefixEnd_1714759 880495573623161731226473 := by
  unfold tailWord_1714759
  simp only [CollatzResearch.WordTrace]
  refine ⟨62542398794728475366731331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694932529818983577820887 62542398794728475366731331)
  ·
    refine ⟨93813598192092713050096997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62542398794728475366731331 93813598192092713050096997)
    ·
      refine ⟨17590049661017383696893187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93813598192092713050096997 17590049661017383696893187)
      ·
        refine ⟨26385074491526075545339781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17590049661017383696893187 26385074491526075545339781)
        ·
          refine ⟨4947201467161139164751209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26385074491526075545339781 4947201467161139164751209)
          ·
            refine ⟨3710401100370854373563407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4947201467161139164751209 3710401100370854373563407)
            ·
              refine ⟨5565601650556281560345111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710401100370854373563407 5565601650556281560345111)
              ·
                refine ⟨8348402475834422340517667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565601650556281560345111 8348402475834422340517667)
                ·
                  refine ⟨12522603713751633510776501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348402475834422340517667 12522603713751633510776501)
                  ·
                    refine ⟨1173994098164215641635297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12522603713751633510776501 1173994098164215641635297)
                    ·
                      refine ⟨880495573623161731226473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173994098164215641635297 880495573623161731226473)
                      ·
                        rfl

theorem cell23_1714759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_1714759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714759 prefixEnd_1714759 := by exact prefixLift 1714759
  have htrace : WordTrace (prefixWord ++ tailWord_1714759) baseStart_1714759 baseEnd_1714759 := by
    simpa [prefixWord, tailWord_1714759, baseEnd_1714759] using wordTrace_append hprefix tailTrace_1714759
  have hstable : (prefixWord ++ tailWord_1714759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714759).length < 2 ^ (prefixWord ++ tailWord_1714759).sum := by decide
  have hdescent : baseEnd_1714759 < baseStart_1714759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714766 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_1714766 : Nat := 118140960795 + 1714766 * 2 ^ 59
def prefixEnd_1714766 : Nat := 4983230072969 + 3 ^ 40 * 1714766 * 2
def baseEnd_1714766 : Nat := 880499167987743203838941

theorem tailTrace_1714766 : CollatzResearch.WordTrace tailWord_1714766 prefixEnd_1714766 880499167987743203838941 := by
  unfold tailWord_1714766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817831763212889445279519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41695102737135410374824101 7817831763212889445279519)
  ·
    refine ⟨11726747644819334167919279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7817831763212889445279519 11726747644819334167919279)
    ·
      refine ⟨17590121467229001251878919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726747644819334167919279 17590121467229001251878919)
      ·
        refine ⟨26385182200843501877818379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17590121467229001251878919 26385182200843501877818379)
        ·
          refine ⟨39577773301265252816727569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26385182200843501877818379 39577773301265252816727569)
          ·
            refine ⟨29683329975948939612545677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39577773301265252816727569 29683329975948939612545677)
            ·
              refine ⟨11131248740980852354704629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29683329975948939612545677 11131248740980852354704629)
              ·
                refine ⟨1043554569466954908253559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11131248740980852354704629 1043554569466954908253559)
                ·
                  refine ⟨1565331854200432362380339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043554569466954908253559 1565331854200432362380339)
                  ·
                    refine ⟨2347997781300648543570509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565331854200432362380339 2347997781300648543570509)
                    ·
                      refine ⟨880499167987743203838941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347997781300648543570509 880499167987743203838941)
                      ·
                        rfl

theorem cell23_1714766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_1714766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714766 prefixEnd_1714766 := by exact prefixLift 1714766
  have htrace : WordTrace (prefixWord ++ tailWord_1714766) baseStart_1714766 baseEnd_1714766 := by
    simpa [prefixWord, tailWord_1714766, baseEnd_1714766] using wordTrace_append hprefix tailTrace_1714766
  have hstable : (prefixWord ++ tailWord_1714766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714766).length < 2 ^ (prefixWord ++ tailWord_1714766).sum := by decide
  have hdescent : baseEnd_1714766 < baseStart_1714766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714769 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 1, 5]
def baseStart_1714769 : Nat := 118140960795 + 1714769 * 2 ^ 59
def prefixEnd_1714769 : Nat := 4983230072969 + 3 ^ 40 * 1714769 * 2
def baseEnd_1714769 : Nat := 293500236143235564033809

theorem tailTrace_1714769 : CollatzResearch.WordTrace tailWord_1714769 prefixEnd_1714769 293500236143235564033809 := by
  unfold tailWord_1714769
  simp only [CollatzResearch.WordTrace]
  refine ⟨62542763524692247074595361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41695175683128164716396907 62542763524692247074595361)
  ·
    refine ⟨46907072643519185305946521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62542763524692247074595361 46907072643519185305946521)
    ·
      refine ⟨35180304482639388979459891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46907072643519185305946521 35180304482639388979459891)
      ·
        refine ⟨52770456723959083469189837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35180304482639388979459891 52770456723959083469189837)
        ·
          refine ⟨19788921271484656300946189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52770456723959083469189837 19788921271484656300946189)
          ·
            refine ⟨7420845476806746112854821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19788921271484656300946189 7420845476806746112854821)
            ·
              refine ⟨1391408526901264896160279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7420845476806746112854821 1391408526901264896160279)
              ·
                refine ⟨2087112790351897344240419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391408526901264896160279 2087112790351897344240419)
                ·
                  refine ⟨3130669185527846016360629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087112790351897344240419 3130669185527846016360629)
                  ·
                    refine ⟨293500236143235564033809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3130669185527846016360629 293500236143235564033809)
                    ·
                      rfl

theorem cell23_1714769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_1714769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714769 prefixEnd_1714769 := by exact prefixLift 1714769
  have htrace : WordTrace (prefixWord ++ tailWord_1714769) baseStart_1714769 baseEnd_1714769 := by
    simpa [prefixWord, tailWord_1714769, baseEnd_1714769] using wordTrace_append hprefix tailTrace_1714769
  have hstable : (prefixWord ++ tailWord_1714769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714769).length < 2 ^ (prefixWord ++ tailWord_1714769).sum := by decide
  have hdescent : baseEnd_1714769 < baseStart_1714769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714809 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1714809 : Nat := 118140960795 + 1714809 * 2 ^ 59
def prefixEnd_1714809 : Nat := 4983230072969 + 3 ^ 40 * 1714809 * 2
def baseEnd_1714809 : Nat := 880521247655886535601243

theorem tailTrace_1714809 : CollatzResearch.WordTrace tailWord_1714809 prefixEnd_1714809 880521247655886535601243 := by
  unfold tailWord_1714809
  simp only [CollatzResearch.WordTrace]
  refine ⟨62544222444547333906051481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41696148296364889270700987 62544222444547333906051481)
  ·
    refine ⟨46908166833410500429538611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62544222444547333906051481 46908166833410500429538611)
    ·
      refine ⟨70362250250115750644307917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46908166833410500429538611 70362250250115750644307917)
      ·
        refine ⟨26385843843793406491615469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70362250250115750644307917 26385843843793406491615469)
        ·
          refine ⟨9894691441422527434355801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26385843843793406491615469 9894691441422527434355801)
          ·
            refine ⟨7421018581066895575766851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894691441422527434355801 7421018581066895575766851)
            ·
              refine ⟨11131527871600343363650277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421018581066895575766851 11131527871600343363650277)
              ·
                refine ⟨2087161475925064380684427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11131527871600343363650277 2087161475925064380684427)
                ·
                  refine ⟨3130742213887596571026641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087161475925064380684427 3130742213887596571026641)
                  ·
                    refine ⟨2348056660415697428269981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130742213887596571026641 2348056660415697428269981)
                    ·
                      refine ⟨880521247655886535601243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2348056660415697428269981 880521247655886535601243)
                      ·
                        rfl

theorem cell23_1714809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1714809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714809 prefixEnd_1714809 := by exact prefixLift 1714809
  have htrace : WordTrace (prefixWord ++ tailWord_1714809) baseStart_1714809 baseEnd_1714809 := by
    simpa [prefixWord, tailWord_1714809, baseEnd_1714809] using wordTrace_append hprefix tailTrace_1714809
  have hstable : (prefixWord ++ tailWord_1714809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714809).length < 2 ^ (prefixWord ++ tailWord_1714809).sum := by decide
  have hdescent : baseEnd_1714809 < baseStart_1714809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714812 : List Nat := [2, 2, 2, 1, 1, 2, 6, 7]
def baseStart_1714812 : Nat := 118140960795 + 1714812 * 2 ^ 59
def prefixEnd_1714812 : Nat := 4983230072969 + 3 ^ 40 * 1714812 * 2
def baseEnd_1714812 : Nat := 32611955114735186069027

theorem tailTrace_1714812 : CollatzResearch.WordTrace tailWord_1714812 prefixEnd_1714812 32611955114735186069027 := by
  unfold tailWord_1714812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272165931768232709205345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41696221242357643612273793 31272165931768232709205345)
  ·
    refine ⟨23454124448826174531904009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31272165931768232709205345 23454124448826174531904009)
    ·
      refine ⟨17590593336619630898928007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23454124448826174531904009 17590593336619630898928007)
      ·
        refine ⟨26385890004929446348392011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17590593336619630898928007 26385890004929446348392011)
        ·
          refine ⟨39578835007394169522588017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26385890004929446348392011 39578835007394169522588017)
          ·
            refine ⟨29684126255545627141941013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39578835007394169522588017 29684126255545627141941013)
            ·
              refine ⟨1391443418228701272278485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29684126255545627141941013 1391443418228701272278485)
              ·
                refine ⟨32611955114735186069027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1391443418228701272278485 32611955114735186069027)
                ·
                  rfl

theorem cell23_1714812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 7].length) (baseStart_1714812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714812 prefixEnd_1714812 := by exact prefixLift 1714812
  have htrace : WordTrace (prefixWord ++ tailWord_1714812) baseStart_1714812 baseEnd_1714812 := by
    simpa [prefixWord, tailWord_1714812, baseEnd_1714812] using wordTrace_append hprefix tailTrace_1714812
  have hstable : (prefixWord ++ tailWord_1714812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714812).length < 2 ^ (prefixWord ++ tailWord_1714812).sum := by decide
  have hdescent : baseEnd_1714812 < baseStart_1714812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714825 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_1714825 : Nat := 118140960795 + 1714825 * 2 ^ 59
def prefixEnd_1714825 : Nat := 4983230072969 + 3 ^ 40 * 1714825 * 2
def baseEnd_1714825 : Nat := 293509821115452824333723

theorem tailTrace_1714825 : CollatzResearch.WordTrace tailWord_1714825 prefixEnd_1714825 293509821115452824333723 := by
  unfold tailWord_1714825
  simp only [CollatzResearch.WordTrace]
  refine ⟨62544806012489368638633929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41696537341659579092422619 62544806012489368638633929)
  ·
    refine ⟨46908604509367026478975447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62544806012489368638633929 46908604509367026478975447)
    ·
      refine ⟨70362906764050539718463171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46908604509367026478975447 70362906764050539718463171)
      ·
        refine ⟨105544360146075809577694757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70362906764050539718463171 105544360146075809577694757)
        ·
          refine ⟨19789567527389214295817767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105544360146075809577694757 19789567527389214295817767)
          ·
            refine ⟨29684351291083821443726651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789567527389214295817767 29684351291083821443726651)
            ·
              refine ⟨44526526936625732165589977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29684351291083821443726651 44526526936625732165589977)
              ·
                refine ⟨33394895202469299124192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44526526936625732165589977 33394895202469299124192483)
                ·
                  refine ⟨50092342803703948686288725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33394895202469299124192483 50092342803703948686288725)
                  ·
                    refine ⟨293509821115452824333723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50092342803703948686288725 293509821115452824333723)
                    ·
                      rfl

theorem cell23_1714825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_1714825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714825 prefixEnd_1714825 := by exact prefixLift 1714825
  have htrace : WordTrace (prefixWord ++ tailWord_1714825) baseStart_1714825 baseEnd_1714825 := by
    simpa [prefixWord, tailWord_1714825, baseEnd_1714825] using wordTrace_append hprefix tailTrace_1714825
  have hstable : (prefixWord ++ tailWord_1714825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714825).length < 2 ^ (prefixWord ++ tailWord_1714825).sum := by decide
  have hdescent : baseEnd_1714825 < baseStart_1714825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714839 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1714839 : Nat := 118140960795 + 1714839 * 2 ^ 59
def prefixEnd_1714839 : Nat := 4983230072969 + 3 ^ 40 * 1714839 * 2
def baseEnd_1714839 : Nat := 880536652075521418226105

theorem tailTrace_1714839 : CollatzResearch.WordTrace tailWord_1714839 prefixEnd_1714839 880536652075521418226105 := by
  unfold tailWord_1714839
  simp only [CollatzResearch.WordTrace]
  refine ⟨62545316634438649029643571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41696877756292432686429047 62545316634438649029643571)
  ·
    refine ⟨93817974951657973544465357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62545316634438649029643571 93817974951657973544465357)
    ·
      refine ⟨35181740606871740079174509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93817974951657973544465357 35181740606871740079174509)
      ·
        refine ⟨13193152727576902529690441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35181740606871740079174509 13193152727576902529690441)
        ·
          refine ⟨9894864545682676897267831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13193152727576902529690441 9894864545682676897267831)
          ·
            refine ⟨14842296818524015345901747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894864545682676897267831 14842296818524015345901747)
            ·
              refine ⟨22263445227786023018852621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14842296818524015345901747 22263445227786023018852621)
              ·
                refine ⟨8348791960419758632069733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22263445227786023018852621 8348791960419758632069733)
                ·
                  refine ⟨1565398492578704743513075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8348791960419758632069733 1565398492578704743513075)
                  ·
                    refine ⟨2348097738868057115269613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565398492578704743513075 2348097738868057115269613)
                    ·
                      refine ⟨880536652075521418226105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2348097738868057115269613 880536652075521418226105)
                      ·
                        rfl

theorem cell23_1714839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1714839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714839 prefixEnd_1714839 := by exact prefixLift 1714839
  have htrace : WordTrace (prefixWord ++ tailWord_1714839) baseStart_1714839 baseEnd_1714839 := by
    simpa [prefixWord, tailWord_1714839, baseEnd_1714839] using wordTrace_append hprefix tailTrace_1714839
  have hstable : (prefixWord ++ tailWord_1714839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714839).length < 2 ^ (prefixWord ++ tailWord_1714839).sum := by decide
  have hdescent : baseEnd_1714839 < baseStart_1714839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714840 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 1, 2, 2]
def baseStart_1714840 : Nat := 118140960795 + 1714840 * 2 ^ 59
def prefixEnd_1714840 : Nat := 4983230072969 + 3 ^ 40 * 1714840 * 2
def baseEnd_1714840 : Nat := 880537165556175914313601

theorem tailTrace_1714840 : CollatzResearch.WordTrace tailWord_1714840 prefixEnd_1714840 880537165556175914313601 := by
  unfold tailWord_1714840
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272676553717513100214987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41696902071623350800286649 31272676553717513100214987)
  ·
    refine ⟨46909014830576269650322481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31272676553717513100214987 46909014830576269650322481)
    ·
      refine ⟨35181761122932202237741861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46909014830576269650322481 35181761122932202237741861)
      ·
        refine ⟨6596580210549787919576599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35181761122932202237741861 6596580210549787919576599)
        ·
          refine ⟨9894870315824681879364899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596580210549787919576599 9894870315824681879364899)
          ·
            refine ⟨14842305473737022819047349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894870315824681879364899 14842305473737022819047349)
            ·
              refine ⟨1391466138162845889285689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14842305473737022819047349 1391466138162845889285689)
              ·
                refine ⟨1043599603622134416964267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391466138162845889285689 1043599603622134416964267)
                ·
                  refine ⟨1565399405433201625446401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043599603622134416964267 1565399405433201625446401)
                  ·
                    refine ⟨1174049554074901219084801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565399405433201625446401 1174049554074901219084801)
                    ·
                      refine ⟨880537165556175914313601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174049554074901219084801 880537165556175914313601)
                      ·
                        rfl

theorem cell23_1714840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_1714840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714840 prefixEnd_1714840 := by exact prefixLift 1714840
  have htrace : WordTrace (prefixWord ++ tailWord_1714840) baseStart_1714840 baseEnd_1714840 := by
    simpa [prefixWord, tailWord_1714840, baseEnd_1714840] using wordTrace_append hprefix tailTrace_1714840
  have hstable : (prefixWord ++ tailWord_1714840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714840).length < 2 ^ (prefixWord ++ tailWord_1714840).sum := by decide
  have hdescent : baseEnd_1714840 < baseStart_1714840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714879 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 3, 4, 2]
def baseStart_1714879 : Nat := 118140960795 + 1714879 * 2 ^ 59
def prefixEnd_1714879 : Nat := 4983230072969 + 3 ^ 40 * 1714879 * 2
def baseEnd_1714879 : Nat := 880557191301701261725921

theorem tailTrace_1714879 : CollatzResearch.WordTrace tailWord_1714879 prefixEnd_1714879 880557191301701261725921 := by
  unfold tailWord_1714879
  simp only [CollatzResearch.WordTrace]
  refine ⟨62546775554293735861099691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41697850369529157240733127 62546775554293735861099691)
  ·
    refine ⟨93820163331440603791649537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62546775554293735861099691 93820163331440603791649537)
    ·
      refine ⟨70365122498580452843737153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93820163331440603791649537 70365122498580452843737153)
      ·
        refine ⟨52773841873935339632802865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70365122498580452843737153 52773841873935339632802865)
        ·
          refine ⟨39580381405451504724602149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52773841873935339632802865 39580381405451504724602149)
          ·
            refine ⟨7421321513522157135862903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39580381405451504724602149 7421321513522157135862903)
            ·
              refine ⟨11131982270283235703794355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421321513522157135862903 11131982270283235703794355)
              ·
                refine ⟨16697973405424853555691533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131982270283235703794355 16697973405424853555691533)
                ·
                  refine ⟨6261740027034320083384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16697973405424853555691533 6261740027034320083384325)
                  ·
                    refine ⟨1174076255068935015634561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261740027034320083384325 1174076255068935015634561)
                    ·
                      refine ⟨880557191301701261725921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174076255068935015634561 880557191301701261725921)
                      ·
                        rfl

theorem cell23_1714879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_1714879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714879 prefixEnd_1714879 := by exact prefixLift 1714879
  have htrace : WordTrace (prefixWord ++ tailWord_1714879) baseStart_1714879 baseEnd_1714879 := by
    simpa [prefixWord, tailWord_1714879, baseEnd_1714879] using wordTrace_append hprefix tailTrace_1714879
  have hstable : (prefixWord ++ tailWord_1714879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714879).length < 2 ^ (prefixWord ++ tailWord_1714879).sum := by decide
  have hdescent : baseEnd_1714879 < baseStart_1714879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714913 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_1714913 : Nat := 118140960795 + 1714913 * 2 ^ 59
def prefixEnd_1714913 : Nat := 4983230072969 + 3 ^ 40 * 1714913 * 2
def baseEnd_1714913 : Nat := 880574649643954128700765

theorem tailTrace_1714913 : CollatzResearch.WordTrace tailWord_1714913 prefixEnd_1714913 880574649643954128700765 := by
  unfold tailWord_1714913
  simp only [CollatzResearch.WordTrace]
  refine ⟨62548015636170559667837393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41698677090780373111891595 62548015636170559667837393)
  ·
    refine ⟨46911011727127919750878045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62548015636170559667837393 46911011727127919750878045)
    ·
      refine ⟨17591629397672969906579267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46911011727127919750878045 17591629397672969906579267)
      ·
        refine ⟨26387444096509454859868901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17591629397672969906579267 26387444096509454859868901)
        ·
          refine ⟨4947645768095522786225419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26387444096509454859868901 4947645768095522786225419)
          ·
            refine ⟨7421468652143284179338129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947645768095522786225419 7421468652143284179338129)
            ·
              refine ⟨5566101489107463134503597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421468652143284179338129 5566101489107463134503597)
              ·
                refine ⟨2087288058415298675438849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5566101489107463134503597 2087288058415298675438849)
                ·
                  refine ⟨1565466043811474006579137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087288058415298675438849 1565466043811474006579137)
                  ·
                    refine ⟨1174099532858605504934353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565466043811474006579137 1174099532858605504934353)
                    ·
                      refine ⟨880574649643954128700765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174099532858605504934353 880574649643954128700765)
                      ·
                        rfl

theorem cell23_1714913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_1714913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714913 prefixEnd_1714913 := by exact prefixLift 1714913
  have htrace : WordTrace (prefixWord ++ tailWord_1714913) baseStart_1714913 baseEnd_1714913 := by
    simpa [prefixWord, tailWord_1714913, baseEnd_1714913] using wordTrace_append hprefix tailTrace_1714913
  have hstable : (prefixWord ++ tailWord_1714913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714913).length < 2 ^ (prefixWord ++ tailWord_1714913).sum := by decide
  have hdescent : baseEnd_1714913 < baseStart_1714913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714946 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1714946 : Nat := 118140960795 + 1714946 * 2 ^ 59
def prefixEnd_1714946 : Nat := 4983230072969 + 3 ^ 40 * 1714946 * 2
def baseEnd_1714946 : Nat := 880591594505552499588113

theorem tailTrace_1714946 : CollatzResearch.WordTrace tailWord_1714946 prefixEnd_1714946 880591594505552499588113 := by
  unfold tailWord_1714946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15637304811262751575947173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41699479496700670869192461 15637304811262751575947173)
  ·
    refine ⟨2931994652111765920490095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15637304811262751575947173 2931994652111765920490095)
    ·
      refine ⟨4397991978167648880735143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931994652111765920490095 4397991978167648880735143)
      ·
        refine ⟨6596987967251473321102715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397991978167648880735143 6596987967251473321102715)
        ·
          refine ⟨9895481950877209981654073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596987967251473321102715 9895481950877209981654073)
          ·
            refine ⟨7421611463157907486240555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9895481950877209981654073 7421611463157907486240555)
            ·
              refine ⟨11132417194736861229360833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421611463157907486240555 11132417194736861229360833)
              ·
                refine ⟨8349312896052645922020625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11132417194736861229360833 8349312896052645922020625)
                ·
                  refine ⟨6261984672039484441515469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8349312896052645922020625 6261984672039484441515469)
                  ·
                    refine ⟨2348244252014806665568301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6261984672039484441515469 2348244252014806665568301)
                    ·
                      refine ⟨880591594505552499588113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2348244252014806665568301 880591594505552499588113)
                      ·
                        rfl

theorem cell23_1714946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1714946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714946 prefixEnd_1714946 := by exact prefixLift 1714946
  have htrace : WordTrace (prefixWord ++ tailWord_1714946) baseStart_1714946 baseEnd_1714946 := by
    simpa [prefixWord, tailWord_1714946, baseEnd_1714946] using wordTrace_append hprefix tailTrace_1714946
  have hstable : (prefixWord ++ tailWord_1714946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714946).length < 2 ^ (prefixWord ++ tailWord_1714946).sum := by decide
  have hdescent : baseEnd_1714946 < baseStart_1714946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714969 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 6, 2]
def baseStart_1714969 : Nat := 118140960795 + 1714969 * 2 ^ 59
def prefixEnd_1714969 : Nat := 4983230072969 + 3 ^ 40 * 1714969 * 2
def baseEnd_1714969 : Nat := 880603404560605909600507

theorem tailTrace_1714969 : CollatzResearch.WordTrace tailWord_1714969 prefixEnd_1714969 880603404560605909600507 := by
  unfold tailWord_1714969
  simp only [CollatzResearch.WordTrace]
  refine ⟨62550058123967681231875961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41700038749311787487917307 62550058123967681231875961)
  ·
    refine ⟨46912543592975760923906971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62550058123967681231875961 46912543592975760923906971)
    ·
      refine ⟨70368815389463641385860457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46912543592975760923906971 70368815389463641385860457)
      ·
        refine ⟨52776611542097731039395343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70368815389463641385860457 52776611542097731039395343)
        ·
          refine ⟨79164917313146596559093015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52776611542097731039395343 79164917313146596559093015)
          ·
            refine ⟨118747375969719894838639523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79164917313146596559093015 118747375969719894838639523)
            ·
              refine ⟨178121063954579842257959285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118747375969719894838639523 178121063954579842257959285)
              ·
                refine ⟨16698849745741860211683683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178121063954579842257959285 16698849745741860211683683)
                ·
                  refine ⟨25048274618612790317525525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16698849745741860211683683 25048274618612790317525525)
                  ·
                    refine ⟨1174137872747474546134009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25048274618612790317525525 1174137872747474546134009)
                    ·
                      refine ⟨880603404560605909600507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174137872747474546134009 880603404560605909600507)
                      ·
                        rfl

theorem cell23_1714969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_1714969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714969 prefixEnd_1714969 := by exact prefixLift 1714969
  have htrace : WordTrace (prefixWord ++ tailWord_1714969) baseStart_1714969 baseEnd_1714969 := by
    simpa [prefixWord, tailWord_1714969, baseEnd_1714969] using wordTrace_append hprefix tailTrace_1714969
  have hstable : (prefixWord ++ tailWord_1714969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714969).length < 2 ^ (prefixWord ++ tailWord_1714969).sum := by decide
  have hdescent : baseEnd_1714969 < baseStart_1714969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715039 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 3, 5]
def baseStart_1715039 : Nat := 118140960795 + 1715039 * 2 ^ 59
def prefixEnd_1715039 : Nat := 4983230072969 + 3 ^ 40 * 1715039 * 2
def baseEnd_1715039 : Nat := 293546449402140211908395

theorem tailTrace_1715039 : CollatzResearch.WordTrace tailWord_1715039 prefixEnd_1715039 293546449402140211908395 := by
  unfold tailWord_1715039
  simp only [CollatzResearch.WordTrace]
  refine ⟨62552611233714083186924171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41701740822476055457949447 62552611233714083186924171)
  ·
    refine ⟨93828916850571124780386257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62552611233714083186924171 93828916850571124780386257)
    ·
      refine ⟨70371687637928343585289693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93828916850571124780386257 70371687637928343585289693)
      ·
        refine ⟨26389382864223128844483635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70371687637928343585289693 26389382864223128844483635)
        ·
          refine ⟨39584074296334693266725453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26389382864223128844483635 39584074296334693266725453)
          ·
            refine ⟨14844027861125509975022045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39584074296334693266725453 14844027861125509975022045)
            ·
              refine ⟨5566510447922066240633267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14844027861125509975022045 5566510447922066240633267)
              ·
                refine ⟨8349765671883099360949901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566510447922066240633267 8349765671883099360949901)
                ·
                  refine ⟨3131162126956162260356213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8349765671883099360949901 3131162126956162260356213)
                  ·
                    refine ⟨293546449402140211908395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3131162126956162260356213 293546449402140211908395)
                    ·
                      rfl

theorem cell23_1715039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_1715039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715039 prefixEnd_1715039 := by exact prefixLift 1715039
  have htrace : WordTrace (prefixWord ++ tailWord_1715039) baseStart_1715039 baseEnd_1715039 := by
    simpa [prefixWord, tailWord_1715039, baseEnd_1715039] using wordTrace_append hprefix tailTrace_1715039
  have hstable : (prefixWord ++ tailWord_1715039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715039).length < 2 ^ (prefixWord ++ tailWord_1715039).sum := by decide
  have hdescent : baseEnd_1715039 < baseStart_1715039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715076 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1715076 : Nat := 118140960795 + 1715076 * 2 ^ 59
def prefixEnd_1715076 : Nat := 4983230072969 + 3 ^ 40 * 1715076 * 2
def baseEnd_1715076 : Nat := 880658346990636990962515

theorem tailTrace_1715076 : CollatzResearch.WordTrace tailWord_1715076 prefixEnd_1715076 880658346990636990962515 := by
  unfold tailWord_1715076
  simp only [CollatzResearch.WordTrace]
  refine ⟨31276980367290019253010541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41702640489720025670680721 31276980367290019253010541)
  ·
    refine ⟨11728867637733757219878953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31276980367290019253010541 11728867637733757219878953)
    ·
      refine ⟨8796650728300317914909215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11728867637733757219878953 8796650728300317914909215)
      ·
        refine ⟨13194976092450476872363823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8796650728300317914909215 13194976092450476872363823)
        ·
          refine ⟨19792464138675715308545735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13194976092450476872363823 19792464138675715308545735)
          ·
            refine ⟨29688696208013572962818603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19792464138675715308545735 29688696208013572962818603)
            ·
              refine ⟨44533044312020359444227905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29688696208013572962818603 44533044312020359444227905)
              ·
                refine ⟨33399783234015269583170929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44533044312020359444227905 33399783234015269583170929)
                ·
                  refine ⟨25049837425511452187378197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33399783234015269583170929 25049837425511452187378197)
                  ·
                    refine ⟨1174211129320849321283353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25049837425511452187378197 1174211129320849321283353)
                    ·
                      refine ⟨880658346990636990962515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174211129320849321283353 880658346990636990962515)
                      ·
                        rfl

theorem cell23_1715076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1715076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715076 prefixEnd_1715076 := by exact prefixLift 1715076
  have htrace : WordTrace (prefixWord ++ tailWord_1715076) baseStart_1715076 baseEnd_1715076 := by
    simpa [prefixWord, tailWord_1715076, baseEnd_1715076] using wordTrace_append hprefix tailTrace_1715076
  have hstable : (prefixWord ++ tailWord_1715076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715076).length < 2 ^ (prefixWord ++ tailWord_1715076).sum := by decide
  have hdescent : baseEnd_1715076 < baseStart_1715076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715093 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_1715093 : Nat := 118140960795 + 1715093 * 2 ^ 59
def prefixEnd_1715093 : Nat := 4983230072969 + 3 ^ 40 * 1715093 * 2
def baseEnd_1715093 : Nat := 880667076161763424449937

theorem tailTrace_1715093 : CollatzResearch.WordTrace tailWord_1715093 prefixEnd_1715093 880667076161763424449937 := by
  unfold tailWord_1715093
  simp only [CollatzResearch.WordTrace]
  refine ⟨62554580775518450409389933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41703053850345633606259955 62554580775518450409389933)
  ·
    refine ⟨23457967790819418903521225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62554580775518450409389933 23457967790819418903521225)
    ·
      refine ⟨17593475843114564177640919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23457967790819418903521225 17593475843114564177640919)
      ·
        refine ⟨26390213764671846266461379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593475843114564177640919 26390213764671846266461379)
        ·
          refine ⟨39585320647007769399692069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26390213764671846266461379 39585320647007769399692069)
          ·
            refine ⟨7422247621313956762442263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39585320647007769399692069 7422247621313956762442263)
            ·
              refine ⟨11133371431970935143663395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422247621313956762442263 11133371431970935143663395)
              ·
                refine ⟨16700057147956402715495093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133371431970935143663395 16700057147956402715495093)
                ·
                  refine ⟨1565630357620912754577665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16700057147956402715495093 1565630357620912754577665)
                  ·
                    refine ⟨1174222768215684565933249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1565630357620912754577665 1174222768215684565933249)
                    ·
                      refine ⟨880667076161763424449937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174222768215684565933249 880667076161763424449937)
                      ·
                        rfl

theorem cell23_1715093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_1715093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715093 prefixEnd_1715093 := by exact prefixLift 1715093
  have htrace : WordTrace (prefixWord ++ tailWord_1715093) baseStart_1715093 baseEnd_1715093 := by
    simpa [prefixWord, tailWord_1715093, baseEnd_1715093] using wordTrace_append hprefix tailTrace_1715093
  have hstable : (prefixWord ++ tailWord_1715093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715093).length < 2 ^ (prefixWord ++ tailWord_1715093).sum := by decide
  have hdescent : baseEnd_1715093 < baseStart_1715093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715143 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_1715143 : Nat := 118140960795 + 1715143 * 2 ^ 59
def prefixEnd_1715143 : Nat := 4983230072969 + 3 ^ 40 * 1715143 * 2
def baseEnd_1715143 : Nat := 880692750194488228824707

theorem tailTrace_1715143 : CollatzResearch.WordTrace tailWord_1715143 prefixEnd_1715143 880692750194488228824707 := by
  unfold tailWord_1715143
  simp only [CollatzResearch.WordTrace]
  refine ⟨62556404425337308948710083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41704269616891539299140055 62556404425337308948710083)
  ·
    refine ⟨93834606638005963423065125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62556404425337308948710083 93834606638005963423065125)
    ·
      refine ⟨17593988744626118141824711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93834606638005963423065125 17593988744626118141824711)
      ·
        refine ⟨26390983116939177212737067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593988744626118141824711 26390983116939177212737067)
        ·
          refine ⟨39586474675408765819105601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26390983116939177212737067 39586474675408765819105601)
          ·
            refine ⟨29689856006556574364329201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39586474675408765819105601 29689856006556574364329201)
            ·
              refine ⟨22267392004917430773246901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29689856006556574364329201 22267392004917430773246901)
              ·
                refine ⟨2087568000461009134991897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22267392004917430773246901 2087568000461009134991897)
                ·
                  refine ⟨1565676000345756851243923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087568000461009134991897 1565676000345756851243923)
                  ·
                    refine ⟨2348514000518635276865885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1565676000345756851243923 2348514000518635276865885)
                    ·
                      refine ⟨880692750194488228824707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2348514000518635276865885 880692750194488228824707)
                      ·
                        rfl

theorem cell23_1715143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_1715143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715143 prefixEnd_1715143 := by exact prefixLift 1715143
  have htrace : WordTrace (prefixWord ++ tailWord_1715143) baseStart_1715143 baseEnd_1715143 := by
    simpa [prefixWord, tailWord_1715143, baseEnd_1715143] using wordTrace_append hprefix tailTrace_1715143
  have hstable : (prefixWord ++ tailWord_1715143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715143).length < 2 ^ (prefixWord ++ tailWord_1715143).sum := by decide
  have hdescent : baseEnd_1715143 < baseStart_1715143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715156 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1715156 : Nat := 118140960795 + 1715156 * 2 ^ 59
def prefixEnd_1715156 : Nat := 4983230072969 + 3 ^ 40 * 1715156 * 2
def baseEnd_1715156 : Nat := 880699425442996677962147

theorem tailTrace_1715156 : CollatzResearch.WordTrace tailWord_1715156 prefixEnd_1715156 880699425442996677962147 := by
  unfold tailWord_1715156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31278439287145106084466661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41704585716193474779288881 31278439287145106084466661)
  ·
    refine ⟨5864707366339707390837499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31278439287145106084466661 5864707366339707390837499)
    ·
      refine ⟨8797061049509561086256249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5864707366339707390837499 8797061049509561086256249)
      ·
        refine ⟨6597795787132170814692187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797061049509561086256249 6597795787132170814692187)
        ·
          refine ⟨9896693680698256222038281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597795787132170814692187 9896693680698256222038281)
          ·
            refine ⟨7422520260523692166528711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9896693680698256222038281 7422520260523692166528711)
            ·
              refine ⟨11133780390785538249793067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422520260523692166528711 11133780390785538249793067)
              ·
                refine ⟨16700670586178307374689601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133780390785538249793067 16700670586178307374689601)
                ·
                  refine ⟨12525502939633730531017201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16700670586178307374689601 12525502939633730531017201)
                  ·
                    refine ⟨9394127204725297898262901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12525502939633730531017201 9394127204725297898262901)
                    ·
                      refine ⟨880699425442996677962147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9394127204725297898262901 880699425442996677962147)
                      ·
                        rfl

theorem cell23_1715156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1715156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715156 prefixEnd_1715156 := by exact prefixLift 1715156
  have htrace : WordTrace (prefixWord ++ tailWord_1715156) baseStart_1715156 baseEnd_1715156 := by
    simpa [prefixWord, tailWord_1715156, baseEnd_1715156] using wordTrace_append hprefix tailTrace_1715156
  have hstable : (prefixWord ++ tailWord_1715156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715156).length < 2 ^ (prefixWord ++ tailWord_1715156).sum := by decide
  have hdescent : baseEnd_1715156 < baseStart_1715156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715159 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 4, 6]
def baseStart_1715159 : Nat := 118140960795 + 1715159 * 2 ^ 59
def prefixEnd_1715159 : Nat := 4983230072969 + 3 ^ 40 * 1715159 * 2
def baseEnd_1715159 : Nat := 293566988628320055408211

theorem tailTrace_1715159 : CollatzResearch.WordTrace tailWord_1715159 prefixEnd_1715159 293566988628320055408211 := by
  unfold tailWord_1715159
  simp only [CollatzResearch.WordTrace]
  refine ⟨62556987993279343681292531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41704658662186229120861687 62556987993279343681292531)
  ·
    refine ⟨93835481989919015521938797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62556987993279343681292531 93835481989919015521938797)
    ·
      refine ⟨35188305746219630820727049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93835481989919015521938797 35188305746219630820727049)
      ·
        refine ⟨26391229309664723115545287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35188305746219630820727049 26391229309664723115545287)
        ·
          refine ⟨39586843964497084673317931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26391229309664723115545287 39586843964497084673317931)
          ·
            refine ⟨59380265946745627009976897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39586843964497084673317931 59380265946745627009976897)
            ·
              refine ⟨44535199460059220257482673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59380265946745627009976897 44535199460059220257482673)
              ·
                refine ⟨33401399595044415193112005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44535199460059220257482673 33401399595044415193112005)
                ·
                  refine ⟨6262762424070827848708501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33401399595044415193112005 6262762424070827848708501)
                  ·
                    refine ⟨293566988628320055408211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6262762424070827848708501 293566988628320055408211)
                    ·
                      rfl

theorem cell23_1715159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_1715159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715159 prefixEnd_1715159 := by exact prefixLift 1715159
  have htrace : WordTrace (prefixWord ++ tailWord_1715159) baseStart_1715159 baseEnd_1715159 := by
    simpa [prefixWord, tailWord_1715159, baseEnd_1715159] using wordTrace_append hprefix tailTrace_1715159
  have hstable : (prefixWord ++ tailWord_1715159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715159).length < 2 ^ (prefixWord ++ tailWord_1715159).sum := by decide
  have hdescent : baseEnd_1715159 < baseStart_1715159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715188 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1715188 : Nat := 118140960795 + 1715188 * 2 ^ 59
def prefixEnd_1715188 : Nat := 4983230072969 + 3 ^ 40 * 1715188 * 2
def baseEnd_1715188 : Nat := 293571952274646850920667

theorem tailTrace_1715188 : CollatzResearch.WordTrace tailWord_1715188 prefixEnd_1715188 293571952274646850920667 := by
  unfold tailWord_1715188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279022855087140817049109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41705363806782854422732145 31279022855087140817049109)
  ·
    refine ⟨1466204196332209725799177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31279022855087140817049109 1466204196332209725799177)
    ·
      refine ⟨1099653147249157294349383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466204196332209725799177 1099653147249157294349383)
      ·
        refine ⟨1649479720873735941524075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099653147249157294349383 1649479720873735941524075)
        ·
          refine ⟨2474219581310603912286113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649479720873735941524075 2474219581310603912286113)
          ·
            refine ⟨1855664685982952934214585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474219581310603912286113 1855664685982952934214585)
            ·
              refine ⟨1391748514487214700660939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855664685982952934214585 1391748514487214700660939)
              ·
                refine ⟨2087622771730822050991409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391748514487214700660939 2087622771730822050991409)
                ·
                  refine ⟨1565717078798116538243557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087622771730822050991409 1565717078798116538243557)
                  ·
                    refine ⟨293571952274646850920667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565717078798116538243557 293571952274646850920667)
                    ·
                      rfl

theorem cell23_1715188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1715188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715188 prefixEnd_1715188 := by exact prefixLift 1715188
  have htrace : WordTrace (prefixWord ++ tailWord_1715188) baseStart_1715188 baseEnd_1715188 := by
    simpa [prefixWord, tailWord_1715188, baseEnd_1715188] using wordTrace_append hprefix tailTrace_1715188
  have hstable : (prefixWord ++ tailWord_1715188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715188).length < 2 ^ (prefixWord ++ tailWord_1715188).sum := by decide
  have hdescent : baseEnd_1715188 < baseStart_1715188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715209 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_1715209 : Nat := 118140960795 + 1715209 * 2 ^ 59
def prefixEnd_1715209 : Nat := 4983230072969 + 3 ^ 40 * 1715209 * 2
def baseEnd_1715209 : Nat := 880726639917684970599403

theorem tailTrace_1715209 : CollatzResearch.WordTrace tailWord_1715209 prefixEnd_1715209 880726639917684970599403 := by
  unfold tailWord_1715209
  simp only [CollatzResearch.WordTrace]
  refine ⟨62558811643098202220612681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41705874428732134813741787 62558811643098202220612681)
  ·
    refine ⟨46919108732323651665459511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62558811643098202220612681 46919108732323651665459511)
    ·
      refine ⟨70378663098485477498189267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46919108732323651665459511 70378663098485477498189267)
      ·
        refine ⟨105567994647728216247283901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70378663098485477498189267 105567994647728216247283901)
        ·
          refine ⟨39587997992898081092731463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105567994647728216247283901 39587997992898081092731463)
          ·
            refine ⟨59381996989347121639097195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39587997992898081092731463 59381996989347121639097195)
            ·
              refine ⟨89072995484020682458645793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59381996989347121639097195 89072995484020682458645793)
              ·
                refine ⟨66804746613015511843984345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89072995484020682458645793 66804746613015511843984345)
                ·
                  refine ⟨50103559959761633882988259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66804746613015511843984345 50103559959761633882988259)
                  ·
                    refine ⟨75155339939642450824482389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50103559959761633882988259 75155339939642450824482389)
                    ·
                      refine ⟨880726639917684970599403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75155339939642450824482389 880726639917684970599403)
                      ·
                        rfl

theorem cell23_1715209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_1715209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715209 prefixEnd_1715209 := by exact prefixLift 1715209
  have htrace : WordTrace (prefixWord ++ tailWord_1715209) baseStart_1715209 baseEnd_1715209 := by
    simpa [prefixWord, tailWord_1715209, baseEnd_1715209] using wordTrace_append hprefix tailTrace_1715209
  have hstable : (prefixWord ++ tailWord_1715209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715209).length < 2 ^ (prefixWord ++ tailWord_1715209).sum := by decide
  have hdescent : baseEnd_1715209 < baseStart_1715209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715270 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1715270 : Nat := 118140960795 + 1715270 * 2 ^ 59
def prefixEnd_1715270 : Nat := 4983230072969 + 3 ^ 40 * 1715270 * 2
def baseEnd_1715270 : Nat := 293585987412536410645541

theorem tailTrace_1715270 : CollatzResearch.WordTrace tailWord_1715270 prefixEnd_1715270 293585987412536410645541 := by
  unfold tailWord_1715270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955032390496162801205727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41707357663918139759055509 1955032390496162801205727)
  ·
    refine ⟨2932548585744244201808591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1955032390496162801205727 2932548585744244201808591)
    ·
      refine ⟨4398822878616366302712887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932548585744244201808591 4398822878616366302712887)
      ·
        refine ⟨6598234317924549454069331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398822878616366302712887 6598234317924549454069331)
        ·
          refine ⟨9897351476886824181103997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598234317924549454069331 9897351476886824181103997)
          ·
            refine ⟨3711506803832559067913999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9897351476886824181103997 3711506803832559067913999)
            ·
              refine ⟨5567260205748838601870999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711506803832559067913999 5567260205748838601870999)
              ·
                refine ⟨8350890308623257902806499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567260205748838601870999 8350890308623257902806499)
                ·
                  refine ⟨12526335462934886854209749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350890308623257902806499 12526335462934886854209749)
                  ·
                    refine ⟨293585987412536410645541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12526335462934886854209749 293585987412536410645541)
                    ·
                      rfl

theorem cell23_1715270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1715270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715270 prefixEnd_1715270 := by exact prefixLift 1715270
  have htrace : WordTrace (prefixWord ++ tailWord_1715270) baseStart_1715270 baseEnd_1715270 := by
    simpa [prefixWord, tailWord_1715270, baseEnd_1715270] using wordTrace_append hprefix tailTrace_1715270
  have hstable : (prefixWord ++ tailWord_1715270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715270).length < 2 ^ (prefixWord ++ tailWord_1715270).sum := by decide
  have hdescent : baseEnd_1715270 < baseStart_1715270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715296 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 8]
def baseStart_1715296 : Nat := 118140960795 + 1715296 * 2 ^ 59
def prefixEnd_1715296 : Nat := 4983230072969 + 3 ^ 40 * 1715296 * 2
def baseEnd_1715296 : Nat := 97863479192736236690167

theorem tailTrace_1715296 : CollatzResearch.WordTrace tailWord_1715296 prefixEnd_1715296 97863479192736236690167 := by
  unfold tailWord_1715296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31280992396891508039514871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41707989862522010719353161 31280992396891508039514871)
  ·
    refine ⟨46921488595337262059272307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31280992396891508039514871 46921488595337262059272307)
    ·
      refine ⟨70382232893005893088908461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46921488595337262059272307 70382232893005893088908461)
      ·
        refine ⟨26393337334877209908340673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70382232893005893088908461 26393337334877209908340673)
        ·
          refine ⟨19795003001157907431255505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26393337334877209908340673 19795003001157907431255505)
          ·
            refine ⟨14846252250868430573441629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19795003001157907431255505 14846252250868430573441629)
            ·
              refine ⟨5567344594075661465040611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14846252250868430573441629 5567344594075661465040611)
              ·
                refine ⟨8351016891113492197560917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567344594075661465040611 8351016891113492197560917)
                ·
                  refine ⟨97863479192736236690167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8351016891113492197560917 97863479192736236690167)
                  ·
                    rfl

theorem cell23_1715296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_1715296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715296 prefixEnd_1715296 := by exact prefixLift 1715296
  have htrace : WordTrace (prefixWord ++ tailWord_1715296) baseStart_1715296 baseEnd_1715296 := by
    simpa [prefixWord, tailWord_1715296, baseEnd_1715296] using wordTrace_append hprefix tailTrace_1715296
  have hstable : (prefixWord ++ tailWord_1715296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715296).length < 2 ^ (prefixWord ++ tailWord_1715296).sum := by decide
  have hdescent : baseEnd_1715296 < baseStart_1715296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715377 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_1715377 : Nat := 118140960795 + 1715377 * 2 ^ 59
def prefixEnd_1715377 : Nat := 4983230072969 + 3 ^ 40 * 1715377 * 2
def baseEnd_1715377 : Nat := 293604301555880104432877

theorem tailTrace_1715377 : CollatzResearch.WordTrace tailWord_1715377 prefixEnd_1715377 293604301555880104432877 := by
  unfold tailWord_1715377
  simp only [CollatzResearch.WordTrace]
  refine ⟨62564939106489566912728385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41709959404326377941818923 62564939106489566912728385)
  ·
    refine ⟨46923704329867175184546289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62564939106489566912728385 46923704329867175184546289)
    ·
      refine ⟨35192778247400381388409717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46923704329867175184546289 35192778247400381388409717)
      ·
        refine ⟨3299322960693785755163411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35192778247400381388409717 3299322960693785755163411)
        ·
          refine ⟨4948984441040678632745117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299322960693785755163411 4948984441040678632745117)
          ·
            refine ⟨1855869165390254487279419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4948984441040678632745117 1855869165390254487279419)
            ·
              refine ⟨2783803748085381730919129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855869165390254487279419 2783803748085381730919129)
              ·
                refine ⟨2087852811064036298189347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783803748085381730919129 2087852811064036298189347)
                ·
                  refine ⟨3131779216596054447284021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087852811064036298189347 3131779216596054447284021)
                  ·
                    refine ⟨293604301555880104432877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3131779216596054447284021 293604301555880104432877)
                    ·
                      rfl

theorem cell23_1715377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_1715377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715377 prefixEnd_1715377 := by exact prefixLift 1715377
  have htrace : WordTrace (prefixWord ++ tailWord_1715377) baseStart_1715377 baseEnd_1715377 := by
    simpa [prefixWord, tailWord_1715377, baseEnd_1715377] using wordTrace_append hprefix tailTrace_1715377
  have hstable : (prefixWord ++ tailWord_1715377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715377).length < 2 ^ (prefixWord ++ tailWord_1715377).sum := by decide
  have hdescent : baseEnd_1715377 < baseStart_1715377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715390 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1715390 : Nat := 118140960795 + 1715390 * 2 ^ 59
def prefixEnd_1715390 : Nat := 4983230072969 + 3 ^ 40 * 1715390 * 2
def baseEnd_1715390 : Nat := 293606526638716254145357

theorem tailTrace_1715390 : CollatzResearch.WordTrace tailWord_1715390 prefixEnd_1715390 293606526638716254145357 := by
  unfold tailWord_1715390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820676656930308766618953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41710275503628313421967749 7820676656930308766618953)
  ·
    refine ⟨5865507492697731574964215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7820676656930308766618953 5865507492697731574964215)
    ·
      refine ⟨8798261239046597362446323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865507492697731574964215 8798261239046597362446323)
      ·
        refine ⟨13197391858569896043669485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798261239046597362446323 13197391858569896043669485)
        ·
          refine ⟨4949021946963711016376057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13197391858569896043669485 4949021946963711016376057)
          ·
            refine ⟨3711766460222783262282043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949021946963711016376057 3711766460222783262282043)
            ·
              refine ⟨5567649690334174893423065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711766460222783262282043 5567649690334174893423065)
              ·
                refine ⟨4175737267750631170067299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5567649690334174893423065 4175737267750631170067299)
                ·
                  refine ⟨6263605901625946755100949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175737267750631170067299 6263605901625946755100949)
                  ·
                    refine ⟨293606526638716254145357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6263605901625946755100949 293606526638716254145357)
                    ·
                      rfl

theorem cell23_1715390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1715390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715390 prefixEnd_1715390 := by exact prefixLift 1715390
  have htrace : WordTrace (prefixWord ++ tailWord_1715390) baseStart_1715390 baseEnd_1715390 := by
    simpa [prefixWord, tailWord_1715390, baseEnd_1715390] using wordTrace_append hprefix tailTrace_1715390
  have hstable : (prefixWord ++ tailWord_1715390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715390).length < 2 ^ (prefixWord ++ tailWord_1715390).sum := by decide
  have hdescent : baseEnd_1715390 < baseStart_1715390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715400 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_1715400 : Nat := 118140960795 + 1715400 * 2 ^ 59
def prefixEnd_1715400 : Nat := 4983230072969 + 3 ^ 40 * 1715400 * 2
def baseEnd_1715400 : Nat := 880824714722693723311025

theorem tailTrace_1715400 : CollatzResearch.WordTrace tailWord_1715400 prefixEnd_1715400 880824714722693723311025 := by
  unfold tailWord_1715400
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282888992703120920407827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41710518656937494560543769 31282888992703120920407827)
  ·
    refine ⟨46924333489054681380611741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31282888992703120920407827 46924333489054681380611741)
    ·
      refine ⟨17596625058395505517729403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46924333489054681380611741 17596625058395505517729403)
      ·
        refine ⟨26394937587593258276594105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17596625058395505517729403 26394937587593258276594105)
        ·
          refine ⟨19796203190694943707445579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26394937587593258276594105 19796203190694943707445579)
          ·
            refine ⟨29694304786042415561168369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796203190694943707445579 29694304786042415561168369)
            ·
              refine ⟨22270728589531811670876277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29694304786042415561168369 22270728589531811670876277)
              ·
                refine ⟨2087880805268607344144651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22270728589531811670876277 2087880805268607344144651)
                ·
                  refine ⟨3131821207902911016216977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087880805268607344144651 3131821207902911016216977)
                  ·
                    refine ⟨2348865905927183262162733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3131821207902911016216977 2348865905927183262162733)
                    ·
                      refine ⟨880824714722693723311025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2348865905927183262162733 880824714722693723311025)
                      ·
                        rfl

theorem cell23_1715400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_1715400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715400 prefixEnd_1715400 := by exact prefixLift 1715400
  have htrace : WordTrace (prefixWord ++ tailWord_1715400) baseStart_1715400 baseEnd_1715400 := by
    simpa [prefixWord, tailWord_1715400, baseEnd_1715400] using wordTrace_append hprefix tailTrace_1715400
  have hstable : (prefixWord ++ tailWord_1715400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715400).length < 2 ^ (prefixWord ++ tailWord_1715400).sum := by decide
  have hdescent : baseEnd_1715400 < baseStart_1715400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715540 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1715540 : Nat := 118140960795 + 1715540 * 2 ^ 59
def prefixEnd_1715540 : Nat := 4983230072969 + 3 ^ 40 * 1715540 * 2
def baseEnd_1715540 : Nat := 293632200671441058520127

theorem tailTrace_1715540 : CollatzResearch.WordTrace tailWord_1715540 prefixEnd_1715540 293632200671441058520127 := by
  unfold tailWord_1715540
  simp only [CollatzResearch.WordTrace]
  refine ⟨31285442102449522875456037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41713922803266030500608049 31285442102449522875456037)
  ·
    refine ⟨5866020394209285539148007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31285442102449522875456037 5866020394209285539148007)
    ·
      refine ⟨8799030591313928308722011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5866020394209285539148007 8799030591313928308722011)
      ·
        refine ⟨13198545886970892463083017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8799030591313928308722011 13198545886970892463083017)
        ·
          refine ⟨9898909415228169347312263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13198545886970892463083017 9898909415228169347312263)
          ·
            refine ⟨14848364122842254020968395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9898909415228169347312263 14848364122842254020968395)
            ·
              refine ⟨22272546184263381031452593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14848364122842254020968395 22272546184263381031452593)
              ·
                refine ⟨16704409638197535773589445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22272546184263381031452593 16704409638197535773589445)
                ·
                  refine ⟨3132076807162037957548021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16704409638197535773589445 3132076807162037957548021)
                  ·
                    refine ⟨293632200671441058520127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3132076807162037957548021 293632200671441058520127)
                    ·
                      rfl

theorem cell23_1715540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1715540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715540 prefixEnd_1715540 := by exact prefixLift 1715540
  have htrace : WordTrace (prefixWord ++ tailWord_1715540) baseStart_1715540 baseEnd_1715540 := by
    simpa [prefixWord, tailWord_1715540, baseEnd_1715540] using wordTrace_append hprefix tailTrace_1715540
  have hstable : (prefixWord ++ tailWord_1715540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715540).length < 2 ^ (prefixWord ++ tailWord_1715540).sum := by decide
  have hdescent : baseEnd_1715540 < baseStart_1715540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715542 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1715542 : Nat := 118140960795 + 1715542 * 2 ^ 59
def prefixEnd_1715542 : Nat := 4983230072969 + 3 ^ 40 * 1715542 * 2
def baseEnd_1715542 : Nat := 880897628975632167735373

theorem tailTrace_1715542 : CollatzResearch.WordTrace tailWord_1715542 prefixEnd_1715542 880897628975632167735373 := by
  unfold tailWord_1715542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910684821930737505780305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41713971433927866728323253 3910684821930737505780305)
  ·
    refine ⟨2933013616448053129335229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3910684821930737505780305 2933013616448053129335229)
    ·
      refine ⟨1099880106168019923500711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2933013616448053129335229 1099880106168019923500711)
      ·
        refine ⟨1649820159252029885251067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099880106168019923500711 1649820159252029885251067)
        ·
          refine ⟨2474730238878044827876601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649820159252029885251067 2474730238878044827876601)
          ·
            refine ⟨1856047679158533620907451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474730238878044827876601 1856047679158533620907451)
            ·
              refine ⟨2784071518737800431361177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856047679158533620907451 2784071518737800431361177)
              ·
                refine ⟨2088053639053350323520883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784071518737800431361177 2088053639053350323520883)
                ·
                  refine ⟨3132080458580025485281325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088053639053350323520883 3132080458580025485281325)
                  ·
                    refine ⟨1174530171967509556980497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132080458580025485281325 1174530171967509556980497)
                    ·
                      refine ⟨880897628975632167735373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174530171967509556980497 880897628975632167735373)
                      ·
                        rfl

theorem cell23_1715542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1715542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715542 prefixEnd_1715542 := by exact prefixLift 1715542
  have htrace : WordTrace (prefixWord ++ tailWord_1715542) baseStart_1715542 baseEnd_1715542 := by
    simpa [prefixWord, tailWord_1715542, baseEnd_1715542] using wordTrace_append hprefix tailTrace_1715542
  have hstable : (prefixWord ++ tailWord_1715542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715542).length < 2 ^ (prefixWord ++ tailWord_1715542).sum := by decide
  have hdescent : baseEnd_1715542 < baseStart_1715542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715553 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1715553 : Nat := 118140960795 + 1715553 * 2 ^ 59
def prefixEnd_1715553 : Nat := 4983230072969 + 3 ^ 40 * 1715553 * 2
def baseEnd_1715553 : Nat := 293634425754277208232607

theorem tailTrace_1715553 : CollatzResearch.WordTrace tailWord_1715553 prefixEnd_1715553 293634425754277208232607 := by
  unfold tailWord_1715553
  simp only [CollatzResearch.WordTrace]
  refine ⟨62571358353851948971135313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41714238902567965980756875 62571358353851948971135313)
  ·
    refine ⟨46928518765388961728351485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62571358353851948971135313 46928518765388961728351485)
    ·
      refine ⟨17598194537020860648131807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46928518765388961728351485 17598194537020860648131807)
      ·
        refine ⟨26397291805531290972197711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17598194537020860648131807 26397291805531290972197711)
        ·
          refine ⟨39595937708296936458296567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26397291805531290972197711 39595937708296936458296567)
          ·
            refine ⟨59393906562445404687444851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39595937708296936458296567 59393906562445404687444851)
            ·
              refine ⟨89090859843668107031167277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59393906562445404687444851 89090859843668107031167277)
              ·
                refine ⟨33409072441375540136687729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89090859843668107031167277 33409072441375540136687729)
                ·
                  refine ⟨25056804331031655102515797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33409072441375540136687729 25056804331031655102515797)
                  ·
                    refine ⟨293634425754277208232607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25056804331031655102515797 293634425754277208232607)
                    ·
                      rfl

theorem cell23_1715553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1715553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715553 prefixEnd_1715553 := by exact prefixLift 1715553
  have htrace : WordTrace (prefixWord ++ tailWord_1715553) baseStart_1715553 baseEnd_1715553 := by
    simpa [prefixWord, tailWord_1715553, baseEnd_1715553] using wordTrace_append hprefix tailTrace_1715553
  have hstable : (prefixWord ++ tailWord_1715553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715553).length < 2 ^ (prefixWord ++ tailWord_1715553).sum := by decide
  have hdescent : baseEnd_1715553 < baseStart_1715553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715563 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_1715563 : Nat := 118140960795 + 1715563 * 2 ^ 59
def prefixEnd_1715563 : Nat := 4983230072969 + 3 ^ 40 * 1715563 * 2
def baseEnd_1715563 : Nat := 880908412069376585572775

theorem tailTrace_1715563 : CollatzResearch.WordTrace tailWord_1715563 prefixEnd_1715563 880908412069376585572775 := by
  unfold tailWord_1715563
  simp only [CollatzResearch.WordTrace]
  refine ⟨62571723083815720678999343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41714482055877147119332895 62571723083815720678999343)
  ·
    refine ⟨93857584625723581018499015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62571723083815720678999343 93857584625723581018499015)
    ·
      refine ⟨140786376938585371527748523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93857584625723581018499015 140786376938585371527748523)
      ·
        refine ⟨211179565407878057291622785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140786376938585371527748523 211179565407878057291622785)
        ·
          refine ⟨158384674055908542968717089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211179565407878057291622785 158384674055908542968717089)
          ·
            refine ⟨118788505541931407226537817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158384674055908542968717089 118788505541931407226537817)
            ·
              refine ⟨89091379156448555419903363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118788505541931407226537817 89091379156448555419903363)
              ·
                refine ⟨133637068734672833129855045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89091379156448555419903363 133637068734672833129855045)
                ·
                  refine ⟨25056950387751156211847821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133637068734672833129855045 25056950387751156211847821)
                  ·
                    refine ⟨9396356395406683579442933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25056950387751156211847821 9396356395406683579442933)
                    ·
                      refine ⟨880908412069376585572775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9396356395406683579442933 880908412069376585572775)
                      ·
                        rfl

theorem cell23_1715563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_1715563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715563 prefixEnd_1715563 := by exact prefixLift 1715563
  have htrace : WordTrace (prefixWord ++ tailWord_1715563) baseStart_1715563 baseEnd_1715563 := by
    simpa [prefixWord, tailWord_1715563, baseEnd_1715563] using wordTrace_append hprefix tailTrace_1715563
  have hstable : (prefixWord ++ tailWord_1715563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715563).length < 2 ^ (prefixWord ++ tailWord_1715563).sum := by decide
  have hdescent : baseEnd_1715563 < baseStart_1715563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715604 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1715604 : Nat := 118140960795 + 1715604 * 2 ^ 59
def prefixEnd_1715604 : Nat := 4983230072969 + 3 ^ 40 * 1715604 * 2
def baseEnd_1715604 : Nat := 293643154925403641720029

theorem tailTrace_1715604 : CollatzResearch.WordTrace tailWord_1715604 prefixEnd_1715604 293643154925403641720029 := by
  unfold tailWord_1715604
  simp only [CollatzResearch.WordTrace]
  refine ⟨31286609238333592340620933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41715478984444789787494577 31286609238333592340620933)
  ·
    refine ⟨5866239232187548563866425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31286609238333592340620933 5866239232187548563866425)
    ·
      refine ⟨4399679424140661422899819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5866239232187548563866425 4399679424140661422899819)
      ·
        refine ⟨6599519136210992134349729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399679424140661422899819 6599519136210992134349729)
        ·
          refine ⟨4949639352158244100762297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599519136210992134349729 4949639352158244100762297)
          ·
            refine ⟨3712229514118683075571723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949639352158244100762297 3712229514118683075571723)
            ·
              refine ⟨5568344271178024613357585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712229514118683075571723 5568344271178024613357585)
              ·
                refine ⟨4176258203383518460018189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5568344271178024613357585 4176258203383518460018189)
                ·
                  refine ⟨1566096826268819422506821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4176258203383518460018189 1566096826268819422506821)
                  ·
                    refine ⟨293643154925403641720029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566096826268819422506821 293643154925403641720029)
                    ·
                      rfl

theorem cell23_1715604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1715604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715604 prefixEnd_1715604 := by exact prefixLift 1715604
  have htrace : WordTrace (prefixWord ++ tailWord_1715604) baseStart_1715604 baseEnd_1715604 := by
    simpa [prefixWord, tailWord_1715604, baseEnd_1715604] using wordTrace_append hprefix tailTrace_1715604
  have hstable : (prefixWord ++ tailWord_1715604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715604).length < 2 ^ (prefixWord ++ tailWord_1715604).sum := by decide
  have hdescent : baseEnd_1715604 < baseStart_1715604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715684 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_1715684 : Nat := 118140960795 + 1715684 * 2 ^ 59
def prefixEnd_1715684 : Nat := 4983230072969 + 3 ^ 40 * 1715684 * 2
def baseEnd_1715684 : Nat := 880970543228570612159719

theorem tailTrace_1715684 : CollatzResearch.WordTrace tailWord_1715684 prefixEnd_1715684 880970543228570612159719 := by
  unfold tailWord_1715684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31288068158188679172077053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41717424210918238896102737 31288068158188679172077053)
  ·
    refine ⟨11733025559320754689528895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31288068158188679172077053 11733025559320754689528895)
    ·
      refine ⟨17599538338981132034293343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11733025559320754689528895 17599538338981132034293343)
      ·
        refine ⟨26399307508471698051440015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17599538338981132034293343 26399307508471698051440015)
        ·
          refine ⟨39598961262707547077160023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26399307508471698051440015 39598961262707547077160023)
          ·
            refine ⟨59398441894061320615740035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39598961262707547077160023 59398441894061320615740035)
            ·
              refine ⟨89097662841091980923610053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59398441894061320615740035 89097662841091980923610053)
              ·
                refine ⟨16705811782704746423176885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89097662841091980923610053 16705811782704746423176885)
                ·
                  refine ⟨1566169854628569977172833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16705811782704746423176885 1566169854628569977172833)
                  ·
                    refine ⟨1174627390971427482879625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1566169854628569977172833 1174627390971427482879625)
                    ·
                      refine ⟨880970543228570612159719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174627390971427482879625 880970543228570612159719)
                      ·
                        rfl

theorem cell23_1715684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_1715684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715684 prefixEnd_1715684 := by exact prefixLift 1715684
  have htrace : WordTrace (prefixWord ++ tailWord_1715684) baseStart_1715684 baseEnd_1715684 := by
    simpa [prefixWord, tailWord_1715684, baseEnd_1715684] using wordTrace_append hprefix tailTrace_1715684
  have hstable : (prefixWord ++ tailWord_1715684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715684).length < 2 ^ (prefixWord ++ tailWord_1715684).sum := by decide
  have hdescent : baseEnd_1715684 < baseStart_1715684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715687 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1715687 : Nat := 118140960795 + 1715687 * 2 ^ 59
def prefixEnd_1715687 : Nat := 4983230072969 + 3 ^ 40 * 1715687 * 2
def baseEnd_1715687 : Nat := 880972083670534100422205

theorem tailTrace_1715687 : CollatzResearch.WordTrace tailWord_1715687 prefixEnd_1715687 880972083670534100422205 := by
  unfold tailWord_1715687
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576245735366489856513315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41717497156910993237675543 62576245735366489856513315)
  ·
    refine ⟨93864368603049734784769973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62576245735366489856513315 93864368603049734784769973)
    ·
      refine ⟨8799784556535912636072185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93864368603049734784769973 8799784556535912636072185)
      ·
        refine ⟨6599838417401934477054139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8799784556535912636072185 6599838417401934477054139)
        ·
          refine ⟨9899757626102901715581209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599838417401934477054139 9899757626102901715581209)
          ·
            refine ⟨7424818219577176286685907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9899757626102901715581209 7424818219577176286685907)
            ·
              refine ⟨11137227329365764430028861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424818219577176286685907 11137227329365764430028861)
              ·
                refine ⟨4176460248512161661260823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11137227329365764430028861 4176460248512161661260823)
                ·
                  refine ⟨6264690372768242491891235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176460248512161661260823 6264690372768242491891235)
                  ·
                    refine ⟨9397035559152363737836853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6264690372768242491891235 9397035559152363737836853)
                    ·
                      refine ⟨880972083670534100422205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9397035559152363737836853 880972083670534100422205)
                      ·
                        rfl

theorem cell23_1715687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1715687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715687 prefixEnd_1715687 := by exact prefixLift 1715687
  have htrace : WordTrace (prefixWord ++ tailWord_1715687) baseStart_1715687 baseEnd_1715687 := by
    simpa [prefixWord, tailWord_1715687, baseEnd_1715687] using wordTrace_append hprefix tailTrace_1715687
  have hstable : (prefixWord ++ tailWord_1715687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715687).length < 2 ^ (prefixWord ++ tailWord_1715687).sum := by decide
  have hdescent : baseEnd_1715687 < baseStart_1715687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715694 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1715694 : Nat := 118140960795 + 1715694 * 2 ^ 59
def prefixEnd_1715694 : Nat := 4983230072969 + 3 ^ 40 * 1715694 * 2
def baseEnd_1715694 : Nat := 293658559345038524344891

theorem tailTrace_1715694 : CollatzResearch.WordTrace tailWord_1715694 prefixEnd_1715694 293658559345038524344891 := by
  unfold tailWord_1715694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7822062630792641256502267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41717667364227420034678757 7822062630792641256502267)
  ·
    refine ⟨11733093946188961884753401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7822062630792641256502267 11733093946188961884753401)
    ·
      refine ⟨8799820459641721413565051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11733093946188961884753401 8799820459641721413565051)
      ·
        refine ⟨13199730689462582120347577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8799820459641721413565051 13199730689462582120347577)
        ·
          refine ⟨9899798017096936590260683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13199730689462582120347577 9899798017096936590260683)
          ·
            refine ⟨14849697025645404885391025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9899798017096936590260683 14849697025645404885391025)
            ·
              refine ⟨11137272769234053664043269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14849697025645404885391025 11137272769234053664043269)
              ·
                refine ⟨2088238644231385062008113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11137272769234053664043269 2088238644231385062008113)
                ·
                  refine ⟨1566178983173538796506085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088238644231385062008113 1566178983173538796506085)
                  ·
                    refine ⟨293658559345038524344891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566178983173538796506085 293658559345038524344891)
                    ·
                      rfl

theorem cell23_1715694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1715694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715694 prefixEnd_1715694 := by exact prefixLift 1715694
  have htrace : WordTrace (prefixWord ++ tailWord_1715694) baseStart_1715694 baseEnd_1715694 := by
    simpa [prefixWord, tailWord_1715694, baseEnd_1715694] using wordTrace_append hprefix tailTrace_1715694
  have hstable : (prefixWord ++ tailWord_1715694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715694).length < 2 ^ (prefixWord ++ tailWord_1715694).sum := by decide
  have hdescent : baseEnd_1715694 < baseStart_1715694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715714 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1715714 : Nat := 118140960795 + 1715714 * 2 ^ 59
def prefixEnd_1715714 : Nat := 4983230072969 + 3 ^ 40 * 1715714 * 2
def baseEnd_1715714 : Nat := 880985947648205494784581

theorem tailTrace_1715714 : CollatzResearch.WordTrace tailWord_1715714 prefixEnd_1715714 880985947648205494784581 := by
  unfold tailWord_1715714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644307626567168366936549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41718153670845782311830797 15644307626567168366936549)
  ·
    refine ⟨2933307679981344068800603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15644307626567168366936549 2933307679981344068800603)
    ·
      refine ⟨4399961519972016103200905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933307679981344068800603 4399961519972016103200905)
      ·
        refine ⟨3299971139979012077400679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399961519972016103200905 3299971139979012077400679)
        ·
          refine ⟨4949956709968518116101019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299971139979012077400679 4949956709968518116101019)
          ·
            refine ⟨7424935064952777174151529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949956709968518116101019 7424935064952777174151529)
            ·
              refine ⟨5568701298714582880613647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7424935064952777174151529 5568701298714582880613647)
              ·
                refine ⟨8353051948071874320920471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568701298714582880613647 8353051948071874320920471)
                ·
                  refine ⟨12529577922107811481380707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8353051948071874320920471 12529577922107811481380707)
                  ·
                    refine ⟨18794366883161717222071061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12529577922107811481380707 18794366883161717222071061)
                    ·
                      refine ⟨880985947648205494784581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18794366883161717222071061 880985947648205494784581)
                      ·
                        rfl

theorem cell23_1715714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1715714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715714 prefixEnd_1715714 := by exact prefixLift 1715714
  have htrace : WordTrace (prefixWord ++ tailWord_1715714) baseStart_1715714 baseEnd_1715714 := by
    simpa [prefixWord, tailWord_1715714, baseEnd_1715714] using wordTrace_append hprefix tailTrace_1715714
  have hstable : (prefixWord ++ tailWord_1715714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715714).length < 2 ^ (prefixWord ++ tailWord_1715714).sum := by decide
  have hdescent : baseEnd_1715714 < baseStart_1715714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715717 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_1715717 : Nat := 118140960795 + 1715717 * 2 ^ 59
def prefixEnd_1715717 : Nat := 4983230072969 + 3 ^ 40 * 1715717 * 2
def baseEnd_1715717 : Nat := 880987488090168983047067

theorem tailTrace_1715717 : CollatzResearch.WordTrace tailWord_1715717 prefixEnd_1715717 880987488090168983047067 := by
  unfold tailWord_1715717
  simp only [CollatzResearch.WordTrace]
  refine ⟨62577339925257804980105405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41718226616838536653403603 62577339925257804980105405)
  ·
    refine ⟨23466502471971676867539527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62577339925257804980105405 23466502471971676867539527)
    ·
      refine ⟨35199753707957515301309291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23466502471971676867539527 35199753707957515301309291)
      ·
        refine ⟨52799630561936272951963937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35199753707957515301309291 52799630561936272951963937)
        ·
          refine ⟨39599722921452204713972953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52799630561936272951963937 39599722921452204713972953)
          ·
            refine ⟨29699792191089153535479715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39599722921452204713972953 29699792191089153535479715)
            ·
              refine ⟨44549688286633730303219573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29699792191089153535479715 44549688286633730303219573)
              ·
                refine ⟨4176533276871912215926835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44549688286633730303219573 4176533276871912215926835)
                ·
                  refine ⟨6264799915307868323890253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176533276871912215926835 6264799915307868323890253)
                  ·
                    refine ⟨2349299968240450621458845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6264799915307868323890253 2349299968240450621458845)
                    ·
                      refine ⟨880987488090168983047067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2349299968240450621458845 880987488090168983047067)
                      ·
                        rfl

theorem cell23_1715717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_1715717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715717 prefixEnd_1715717 := by exact prefixLift 1715717
  have htrace : WordTrace (prefixWord ++ tailWord_1715717) baseStart_1715717 baseEnd_1715717 := by
    simpa [prefixWord, tailWord_1715717, baseEnd_1715717] using wordTrace_append hprefix tailTrace_1715717
  have hstable : (prefixWord ++ tailWord_1715717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715717).length < 2 ^ (prefixWord ++ tailWord_1715717).sum := by decide
  have hdescent : baseEnd_1715717 < baseStart_1715717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715767 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 2, 6]
def baseStart_1715767 : Nat := 118140960795 + 1715767 * 2 ^ 59
def prefixEnd_1715767 : Nat := 4983230072969 + 3 ^ 40 * 1715767 * 2
def baseEnd_1715767 : Nat := 293671054040964595807279

theorem tailTrace_1715767 : CollatzResearch.WordTrace tailWord_1715767 prefixEnd_1715767 293671054040964595807279 := by
  unfold tailWord_1715767
  simp only [CollatzResearch.WordTrace]
  refine ⟨62579163575076663519425555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41719442383384442346283703 62579163575076663519425555)
  ·
    refine ⟨93868745362614995279138333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62579163575076663519425555 93868745362614995279138333)
    ·
      refine ⟨35200779510980623229676875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93868745362614995279138333 35200779510980623229676875)
      ·
        refine ⟨52801169266470934844515313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35200779510980623229676875 52801169266470934844515313)
        ·
          refine ⟨39600876949853201133386485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52801169266470934844515313 39600876949853201133386485)
          ·
            refine ⟨3712582214048737606254983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39600876949853201133386485 3712582214048737606254983)
            ·
              refine ⟨5568873321073106409382475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712582214048737606254983 5568873321073106409382475)
              ·
                refine ⟨8353309981609659614073713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568873321073106409382475 8353309981609659614073713)
                ·
                  refine ⟨6264982486207244710555285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8353309981609659614073713 6264982486207244710555285)
                  ·
                    refine ⟨293671054040964595807279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6264982486207244710555285 293671054040964595807279)
                    ·
                      rfl

theorem cell23_1715767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_1715767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715767 prefixEnd_1715767 := by exact prefixLift 1715767
  have htrace : WordTrace (prefixWord ++ tailWord_1715767) baseStart_1715767 baseEnd_1715767 := by
    simpa [prefixWord, tailWord_1715767, baseEnd_1715767] using wordTrace_append hprefix tailTrace_1715767
  have hstable : (prefixWord ++ tailWord_1715767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715767).length < 2 ^ (prefixWord ++ tailWord_1715767).sum := by decide
  have hdescent : baseEnd_1715767 < baseStart_1715767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715804 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1715804 : Nat := 118140960795 + 1715804 * 2 ^ 59
def prefixEnd_1715804 : Nat := 4983230072969 + 3 ^ 40 * 1715804 * 2
def baseEnd_1715804 : Nat := 881032160907110142659167

theorem tailTrace_1715804 : CollatzResearch.WordTrace tailWord_1715804 prefixEnd_1715804 881032160907110142659167 := by
  unfold tailWord_1715804
  simp only [CollatzResearch.WordTrace]
  refine ⟨31290256537971309419261233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41720342050628412559014977 31290256537971309419261233)
  ·
    refine ⟨23467692403478482064445925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31290256537971309419261233 23467692403478482064445925)
    ·
      refine ⟨4400192325652215387083611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23467692403478482064445925 4400192325652215387083611)
      ·
        refine ⟨6600288488478323080625417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400192325652215387083611 6600288488478323080625417)
        ·
          refine ⟨4950216366358742310469063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6600288488478323080625417 4950216366358742310469063)
          ·
            refine ⟨7425324549538113465703595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950216366358742310469063 7425324549538113465703595)
            ·
              refine ⟨11137986824307170198555393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425324549538113465703595 11137986824307170198555393)
              ·
                refine ⟨8353490118230377648916545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11137986824307170198555393 8353490118230377648916545)
                ·
                  refine ⟨6265117588672783236687409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8353490118230377648916545 6265117588672783236687409)
                  ·
                    refine ⟨4698838191504587427515557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265117588672783236687409 4698838191504587427515557)
                    ·
                      refine ⟨881032160907110142659167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4698838191504587427515557 881032160907110142659167)
                      ·
                        rfl

theorem cell23_1715804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1715804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715804 prefixEnd_1715804 := by exact prefixLift 1715804
  have htrace : WordTrace (prefixWord ++ tailWord_1715804) baseStart_1715804 baseEnd_1715804 := by
    simpa [prefixWord, tailWord_1715804, baseEnd_1715804] using wordTrace_append hprefix tailTrace_1715804
  have hstable : (prefixWord ++ tailWord_1715804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715804).length < 2 ^ (prefixWord ++ tailWord_1715804).sum := by decide
  have hdescent : baseEnd_1715804 < baseStart_1715804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715824 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_1715824 : Nat := 118140960795 + 1715824 * 2 ^ 59
def prefixEnd_1715824 : Nat := 4983230072969 + 3 ^ 40 * 1715824 * 2
def baseEnd_1715824 : Nat := 881042430520200064409075

theorem tailTrace_1715824 : CollatzResearch.WordTrace tailWord_1715824 prefixEnd_1715824 881042430520200064409075 := by
  unfold tailWord_1715824
  simp only [CollatzResearch.WordTrace]
  refine ⟨31290621267935081127125263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41720828357246774836167017 31290621267935081127125263)
  ·
    refine ⟨46935931901902621690687895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31290621267935081127125263 46935931901902621690687895)
    ·
      refine ⟨70403897852853932536031843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46935931901902621690687895 70403897852853932536031843)
      ·
        refine ⟨105605846779280898804047765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70403897852853932536031843 105605846779280898804047765)
        ·
          refine ⟨4950274067778792131439739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105605846779280898804047765 4950274067778792131439739)
          ·
            refine ⟨7425411101668188197159609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950274067778792131439739 7425411101668188197159609)
            ·
              refine ⟨5569058326251141147869707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425411101668188197159609 5569058326251141147869707)
              ·
                refine ⟨8353587489376711721804561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569058326251141147869707 8353587489376711721804561)
                ·
                  refine ⟨6265190617032533791353421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8353587489376711721804561 6265190617032533791353421)
                  ·
                    refine ⟨2349446481387200171757533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6265190617032533791353421 2349446481387200171757533)
                    ·
                      refine ⟨881042430520200064409075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2349446481387200171757533 881042430520200064409075)
                      ·
                        rfl

theorem cell23_1715824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_1715824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715824 prefixEnd_1715824 := by exact prefixLift 1715824
  have htrace : WordTrace (prefixWord ++ tailWord_1715824) baseStart_1715824 baseEnd_1715824 := by
    simpa [prefixWord, tailWord_1715824, baseEnd_1715824] using wordTrace_append hprefix tailTrace_1715824
  have hstable : (prefixWord ++ tailWord_1715824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715824).length < 2 ^ (prefixWord ++ tailWord_1715824).sum := by decide
  have hdescent : baseEnd_1715824 < baseStart_1715824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715864 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1715864 : Nat := 118140960795 + 1715864 * 2 ^ 59
def prefixEnd_1715864 : Nat := 4983230072969 + 3 ^ 40 * 1715864 * 2
def baseEnd_1715864 : Nat := 881062969746379907908891

theorem tailTrace_1715864 : CollatzResearch.WordTrace tailWord_1715864 prefixEnd_1715864 881062969746379907908891 := by
  unfold tailWord_1715864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291350727862624542853323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41721800970483499390471097 31291350727862624542853323)
  ·
    refine ⟨46937026091793936814279985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31291350727862624542853323 46937026091793936814279985)
    ·
      refine ⟨35202769568845452610709989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46937026091793936814279985 35202769568845452610709989)
      ·
        refine ⟨6600519294158522364508123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35202769568845452610709989 6600519294158522364508123)
        ·
          refine ⟨9900778941237783546762185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600519294158522364508123 9900778941237783546762185)
          ·
            refine ⟨7425584205928337660071639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9900778941237783546762185 7425584205928337660071639)
            ·
              refine ⟨11138376308892506490107459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425584205928337660071639 11138376308892506490107459)
              ·
                refine ⟨16707564463338759735161189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11138376308892506490107459 16707564463338759735161189)
                ·
                  refine ⟨3132668336876017450342723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16707564463338759735161189 3132668336876017450342723)
                  ·
                    refine ⟨4699002505314026175514085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3132668336876017450342723 4699002505314026175514085)
                    ·
                      refine ⟨881062969746379907908891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4699002505314026175514085 881062969746379907908891)
                      ·
                        rfl

theorem cell23_1715864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1715864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715864 prefixEnd_1715864 := by exact prefixLift 1715864
  have htrace : WordTrace (prefixWord ++ tailWord_1715864) baseStart_1715864 baseEnd_1715864 := by
    simpa [prefixWord, tailWord_1715864, baseEnd_1715864] using wordTrace_append hprefix tailTrace_1715864
  have hstable : (prefixWord ++ tailWord_1715864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715864).length < 2 ^ (prefixWord ++ tailWord_1715864).sum := by decide
  have hdescent : baseEnd_1715864 < baseStart_1715864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715871 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1715871 : Nat := 118140960795 + 1715871 * 2 ^ 59
def prefixEnd_1715871 : Nat := 4983230072969 + 3 ^ 40 * 1715871 * 2
def baseEnd_1715871 : Nat := 881066564110961380521359

theorem tailTrace_1715871 : CollatzResearch.WordTrace tailWord_1715871 prefixEnd_1715871 881066564110961380521359 := by
  unfold tailWord_1715871
  simp only [CollatzResearch.WordTrace]
  refine ⟨62582956766699889281211467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41721971177799926187474311 62582956766699889281211467)
  ·
    refine ⟨93874435150049833921817201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62582956766699889281211467 93874435150049833921817201)
    ·
      refine ⟨70405826362537375441362901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93874435150049833921817201 70405826362537375441362901)
      ·
        refine ⟨1650136555371969736906943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 70405826362537375441362901 1650136555371969736906943)
        ·
          refine ⟨2475204833057954605360415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650136555371969736906943 2475204833057954605360415)
          ·
            refine ⟨3712807249586931908040623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475204833057954605360415 3712807249586931908040623)
            ·
              refine ⟨5569210874380397862060935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712807249586931908040623 5569210874380397862060935)
              ·
                refine ⟨8353816311570596793091403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569210874380397862060935 8353816311570596793091403)
                ·
                  refine ⟨12530724467355895189637105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8353816311570596793091403 12530724467355895189637105)
                  ·
                    refine ⟨9398043350516921392227829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12530724467355895189637105 9398043350516921392227829)
                    ·
                      refine ⟨881066564110961380521359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9398043350516921392227829 881066564110961380521359)
                      ·
                        rfl

theorem cell23_1715871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1715871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715871 prefixEnd_1715871 := by exact prefixLift 1715871
  have htrace : WordTrace (prefixWord ++ tailWord_1715871) baseStart_1715871 baseEnd_1715871 := by
    simpa [prefixWord, tailWord_1715871, baseEnd_1715871] using wordTrace_append hprefix tailTrace_1715871
  have hstable : (prefixWord ++ tailWord_1715871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715871).length < 2 ^ (prefixWord ++ tailWord_1715871).sum := by decide
  have hdescent : baseEnd_1715871 < baseStart_1715871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715877 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1715877 : Nat := 118140960795 + 1715877 * 2 ^ 59
def prefixEnd_1715877 : Nat := 4983230072969 + 3 ^ 40 * 1715877 * 2
def baseEnd_1715877 : Nat := 881069644994888357046331

theorem tailTrace_1715877 : CollatzResearch.WordTrace tailWord_1715877 prefixEnd_1715877 881069644994888357046331 := by
  unfold tailWord_1715877
  simp only [CollatzResearch.WordTrace]
  refine ⟨62583175604678152305929885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41722117069785434870619923 62583175604678152305929885)
  ·
    refine ⟨23468690851754307114723707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62583175604678152305929885 23468690851754307114723707)
    ·
      refine ⟨35203036277631460672085561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23468690851754307114723707 35203036277631460672085561)
      ·
        refine ⟨26402277208223595504064171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35203036277631460672085561 26402277208223595504064171)
        ·
          refine ⟨39603415812335393256096257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26402277208223595504064171 39603415812335393256096257)
          ·
            refine ⟨29702561859251544942072193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39603415812335393256096257 29702561859251544942072193)
            ·
              refine ⟨22276921394438658706554145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29702561859251544942072193 22276921394438658706554145)
              ·
                refine ⟨16707691045828994029915609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22276921394438658706554145 16707691045828994029915609)
                ·
                  refine ⟨12530768284371745522436707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16707691045828994029915609 12530768284371745522436707)
                  ·
                    refine ⟨18796152426557618283655061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12530768284371745522436707 18796152426557618283655061)
                    ·
                      refine ⟨881069644994888357046331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18796152426557618283655061 881069644994888357046331)
                      ·
                        rfl

theorem cell23_1715877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1715877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715877 prefixEnd_1715877 := by exact prefixLift 1715877
  have htrace : WordTrace (prefixWord ++ tailWord_1715877) baseStart_1715877 baseEnd_1715877 := by
    simpa [prefixWord, tailWord_1715877, baseEnd_1715877] using wordTrace_append hprefix tailTrace_1715877
  have hstable : (prefixWord ++ tailWord_1715877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715877).length < 2 ^ (prefixWord ++ tailWord_1715877).sum := by decide
  have hdescent : baseEnd_1715877 < baseStart_1715877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715901 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1715901 : Nat := 118140960795 + 1715901 * 2 ^ 59
def prefixEnd_1715901 : Nat := 4983230072969 + 3 ^ 40 * 1715901 * 2
def baseEnd_1715901 : Nat := 881081968530596263146221

theorem tailTrace_1715901 : CollatzResearch.WordTrace tailWord_1715901 prefixEnd_1715901 881081968530596263146221 := by
  unfold tailWord_1715901
  simp only [CollatzResearch.WordTrace]
  refine ⟨62584050956591204404803557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41722700637727469603202371 62584050956591204404803557)
  ·
    refine ⟨11734509554360850825900667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62584050956591204404803557 11734509554360850825900667)
    ·
      refine ⟨17601764331541276238851001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11734509554360850825900667 17601764331541276238851001)
      ·
        refine ⟨13201323248655957179138251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17601764331541276238851001 13201323248655957179138251)
        ·
          refine ⟨19801984872983935768707377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201323248655957179138251 19801984872983935768707377)
          ·
            refine ⟨14851488654737951826530533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19801984872983935768707377 14851488654737951826530533)
            ·
              refine ⟨2784654122763365967474475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14851488654737951826530533 2784654122763365967474475)
              ·
                refine ⟨4176981184145048951211713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784654122763365967474475 4176981184145048951211713)
                ·
                  refine ⟨3132735888108786713408785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176981184145048951211713 3132735888108786713408785)
                  ·
                    refine ⟨2349551916081590035056589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132735888108786713408785 2349551916081590035056589)
                    ·
                      refine ⟨881081968530596263146221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2349551916081590035056589 881081968530596263146221)
                      ·
                        rfl

theorem cell23_1715901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1715901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715901 prefixEnd_1715901 := by exact prefixLift 1715901
  have htrace : WordTrace (prefixWord ++ tailWord_1715901) baseStart_1715901 baseEnd_1715901 := by
    simpa [prefixWord, tailWord_1715901, baseEnd_1715901] using wordTrace_append hprefix tailTrace_1715901
  have hstable : (prefixWord ++ tailWord_1715901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715901).length < 2 ^ (prefixWord ++ tailWord_1715901).sum := by decide
  have hdescent : baseEnd_1715901 < baseStart_1715901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715908 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1715908 : Nat := 118140960795 + 1715908 * 2 ^ 59
def prefixEnd_1715908 : Nat := 4983230072969 + 3 ^ 40 * 1715908 * 2
def baseEnd_1715908 : Nat := 293695187631725911919563

theorem tailTrace_1715908 : CollatzResearch.WordTrace tailWord_1715908 prefixEnd_1715908 293695187631725911919563 := by
  unfold tailWord_1715908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292153133782922300154189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41722870845043896400205585 31292153133782922300154189)
  ·
    refine ⟨11734557425168595862557821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31292153133782922300154189 11734557425168595862557821)
    ·
      refine ⟨4400459034438223448459183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11734557425168595862557821 4400459034438223448459183)
      ·
        refine ⟨6600688551657335172688775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400459034438223448459183 6600688551657335172688775)
        ·
          refine ⟨9901032827486002759033163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600688551657335172688775 9901032827486002759033163)
          ·
            refine ⟨14851549241229004138549745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901032827486002759033163 14851549241229004138549745)
            ·
              refine ⟨11138661930921753103912309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14851549241229004138549745 11138661930921753103912309)
              ·
                refine ⟨1044249556023914353491779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11138661930921753103912309 1044249556023914353491779)
                ·
                  refine ⟨1566374334035871530237669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044249556023914353491779 1566374334035871530237669)
                  ·
                    refine ⟨293695187631725911919563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566374334035871530237669 293695187631725911919563)
                    ·
                      rfl

theorem cell23_1715908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1715908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715908 prefixEnd_1715908 := by exact prefixLift 1715908
  have htrace : WordTrace (prefixWord ++ tailWord_1715908) baseStart_1715908 baseEnd_1715908 := by
    simpa [prefixWord, tailWord_1715908, baseEnd_1715908] using wordTrace_append hprefix tailTrace_1715908
  have hstable : (prefixWord ++ tailWord_1715908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715908).length < 2 ^ (prefixWord ++ tailWord_1715908).sum := by decide
  have hdescent : baseEnd_1715908 < baseStart_1715908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715941 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_1715941 : Nat := 118140960795 + 1715941 * 2 ^ 59
def prefixEnd_1715941 : Nat := 4983230072969 + 3 ^ 40 * 1715941 * 2
def baseEnd_1715941 : Nat := 881102507756776106646037

theorem tailTrace_1715941 : CollatzResearch.WordTrace tailWord_1715941 prefixEnd_1715941 881102507756776106646037 := by
  unfold tailWord_1715941
  simp only [CollatzResearch.WordTrace]
  refine ⟨62585509876446291236259677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41723673250964194157506451 62585509876446291236259677)
  ·
    refine ⟨23469566203667359213597379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62585509876446291236259677 23469566203667359213597379)
    ·
      refine ⟨35204349305501038820396069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23469566203667359213597379 35204349305501038820396069)
      ·
        refine ⟨6600815494781444778824263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35204349305501038820396069 6600815494781444778824263)
        ·
          refine ⟨9901223242172167168236395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600815494781444778824263 9901223242172167168236395)
          ·
            refine ⟨14851834863258250752354593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901223242172167168236395 14851834863258250752354593)
            ·
              refine ⟨11138876147443688064265945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14851834863258250752354593 11138876147443688064265945)
              ·
                refine ⟨8354157110582766048199459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11138876147443688064265945 8354157110582766048199459)
                ·
                  refine ⟨12531235665874149072299189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354157110582766048199459 12531235665874149072299189)
                  ·
                    refine ⟨1174803343675701475528049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12531235665874149072299189 1174803343675701475528049)
                    ·
                      refine ⟨881102507756776106646037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174803343675701475528049 881102507756776106646037)
                      ·
                        rfl

theorem cell23_1715941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_1715941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715941 prefixEnd_1715941 := by exact prefixLift 1715941
  have htrace : WordTrace (prefixWord ++ tailWord_1715941) baseStart_1715941 baseEnd_1715941 := by
    simpa [prefixWord, tailWord_1715941, baseEnd_1715941] using wordTrace_append hprefix tailTrace_1715941
  have hstable : (prefixWord ++ tailWord_1715941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715941).length < 2 ^ (prefixWord ++ tailWord_1715941).sum := by decide
  have hdescent : baseEnd_1715941 < baseStart_1715941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715958 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1715958 : Nat := 118140960795 + 1715958 * 2 ^ 59
def prefixEnd_1715958 : Nat := 4983230072969 + 3 ^ 40 * 1715958 * 2
def baseEnd_1715958 : Nat := 881111236927902540133459

theorem tailTrace_1715958 : CollatzResearch.WordTrace tailWord_1715958 prefixEnd_1715958 881111236927902540133459 := by
  unfold tailWord_1715958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911633119836543946226783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41724086611589802093085685 3911633119836543946226783)
  ·
    refine ⟨5867449679754815919340175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3911633119836543946226783 5867449679754815919340175)
    ·
      refine ⟨8801174519632223879010263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867449679754815919340175 8801174519632223879010263)
      ·
        refine ⟨13201761779448335818515395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801174519632223879010263 13201761779448335818515395)
        ·
          refine ⟨19802642669172503727773093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201761779448335818515395 19802642669172503727773093)
          ·
            refine ⟨3712995500469844448957455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19802642669172503727773093 3712995500469844448957455)
            ·
              refine ⟨5569493250704766673436183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712995500469844448957455 5569493250704766673436183)
              ·
                refine ⟨8354239876057150010154275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569493250704766673436183 8354239876057150010154275)
                ·
                  refine ⟨12531359814085725015231413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354239876057150010154275 12531359814085725015231413)
                  ·
                    refine ⟨1174814982570536720177945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12531359814085725015231413 1174814982570536720177945)
                    ·
                      refine ⟨881111236927902540133459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1174814982570536720177945 881111236927902540133459)
                      ·
                        rfl

theorem cell23_1715958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1715958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715958 prefixEnd_1715958 := by exact prefixLift 1715958
  have htrace : WordTrace (prefixWord ++ tailWord_1715958) baseStart_1715958 baseEnd_1715958 := by
    simpa [prefixWord, tailWord_1715958, baseEnd_1715958] using wordTrace_append hprefix tailTrace_1715958
  have hstable : (prefixWord ++ tailWord_1715958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715958).length < 2 ^ (prefixWord ++ tailWord_1715958).sum := by decide
  have hdescent : baseEnd_1715958 < baseStart_1715958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715964 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_1715964 : Nat := 118140960795 + 1715964 * 2 ^ 59
def prefixEnd_1715964 : Nat := 4983230072969 + 3 ^ 40 * 1715964 * 2
def baseEnd_1715964 : Nat := 293704772603943172219477

theorem tailTrace_1715964 : CollatzResearch.WordTrace tailWord_1715964 prefixEnd_1715964 293704772603943172219477 := by
  unfold tailWord_1715964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293174377681483082173473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41724232503575310776231297 31293174377681483082173473)
  ·
    refine ⟨23469880783261112311630105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31293174377681483082173473 23469880783261112311630105)
    ·
      refine ⟨17602410587445834233722579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23469880783261112311630105 17602410587445834233722579)
      ·
        refine ⟨26403615881168751350583869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17602410587445834233722579 26403615881168751350583869)
        ·
          refine ⟨9901355955438281756468951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26403615881168751350583869 9901355955438281756468951)
          ·
            refine ⟨14852033933157422634703427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901355955438281756468951 14852033933157422634703427)
            ·
              refine ⟨22278050899736133952055141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14852033933157422634703427 22278050899736133952055141)
              ·
                refine ⟨4177134543700525116010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22278050899736133952055141 4177134543700525116010339)
                ·
                  refine ⟨6265701815550787674015509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177134543700525116010339 6265701815550787674015509)
                  ·
                    refine ⟨293704772603943172219477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6265701815550787674015509 293704772603943172219477)
                    ·
                      rfl

theorem cell23_1715964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_1715964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715964 prefixEnd_1715964 := by exact prefixLift 1715964
  have htrace : WordTrace (prefixWord ++ tailWord_1715964) baseStart_1715964 baseEnd_1715964 := by
    simpa [prefixWord, tailWord_1715964, baseEnd_1715964] using wordTrace_append hprefix tailTrace_1715964
  have hstable : (prefixWord ++ tailWord_1715964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715964).length < 2 ^ (prefixWord ++ tailWord_1715964).sum := by decide
  have hdescent : baseEnd_1715964 < baseStart_1715964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715991 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1715991 : Nat := 118140960795 + 1715991 * 2 ^ 59
def prefixEnd_1715991 : Nat := 4983230072969 + 3 ^ 40 * 1715991 * 2
def baseEnd_1715991 : Nat := 881128181789500911020807

theorem tailTrace_1715991 : CollatzResearch.WordTrace tailWord_1715991 prefixEnd_1715991 881128181789500911020807 := by
  unfold tailWord_1715991
  simp only [CollatzResearch.WordTrace]
  refine ⟨62587333526265149775579827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41724889017510099850386551 62587333526265149775579827)
  ·
    refine ⟨93881000289397724663369741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62587333526265149775579827 93881000289397724663369741)
    ·
      refine ⟨35205375108524146748763653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93881000289397724663369741 35205375108524146748763653)
      ·
        refine ⟨6601007832848277515393185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35205375108524146748763653 6601007832848277515393185)
        ·
          refine ⟨4950755874636208136544889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6601007832848277515393185 4950755874636208136544889)
          ·
            refine ⟨3713066905977156102408667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4950755874636208136544889 3713066905977156102408667)
            ·
              refine ⟨5569600358965734153613001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713066905977156102408667 5569600358965734153613001)
              ·
                refine ⟨4177200269224300615209751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569600358965734153613001 4177200269224300615209751)
                ·
                  refine ⟨6265800403836450922814627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177200269224300615209751 6265800403836450922814627)
                  ·
                    refine ⟨9398700605754676384221941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6265800403836450922814627 9398700605754676384221941)
                    ·
                      refine ⟨881128181789500911020807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9398700605754676384221941 881128181789500911020807)
                      ·
                        rfl

theorem cell23_1715991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1715991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1715991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1715991 prefixEnd_1715991 := by exact prefixLift 1715991
  have htrace : WordTrace (prefixWord ++ tailWord_1715991) baseStart_1715991 baseEnd_1715991 := by
    simpa [prefixWord, tailWord_1715991, baseEnd_1715991] using wordTrace_append hprefix tailTrace_1715991
  have hstable : (prefixWord ++ tailWord_1715991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715991).length < 2 ^ (prefixWord ++ tailWord_1715991).sum := by decide
  have hdescent : baseEnd_1715991 < baseStart_1715991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716001 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1716001 : Nat := 118140960795 + 1716001 * 2 ^ 59
def prefixEnd_1716001 : Nat := 4983230072969 + 3 ^ 40 * 1716001 * 2
def baseEnd_1716001 : Nat := 881133316596045871895761

theorem tailTrace_1716001 : CollatzResearch.WordTrace tailWord_1716001 prefixEnd_1716001 881133316596045871895761 := by
  unfold tailWord_1716001
  simp only [CollatzResearch.WordTrace]
  refine ⟨62587698256228921483443857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41725132170819280988962571 62587698256228921483443857)
  ·
    refine ⟨46940773692171691112582893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62587698256228921483443857 46940773692171691112582893)
    ·
      refine ⟨17602790134564384167218585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46940773692171691112582893 17602790134564384167218585)
      ·
        refine ⟨13202092600923288125413939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17602790134564384167218585 13202092600923288125413939)
        ·
          refine ⟨19803138901384932188120909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202092600923288125413939 19803138901384932188120909)
          ·
            refine ⟨7426177088019349570545341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19803138901384932188120909 7426177088019349570545341)
            ·
              refine ⟨2784816408007256088954503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7426177088019349570545341 2784816408007256088954503)
              ·
                refine ⟨4177224612010884133431755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784816408007256088954503 4177224612010884133431755)
                ·
                  refine ⟨6265836918016326200147633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177224612010884133431755 6265836918016326200147633)
                  ·
                    refine ⟨4699377688512244650110725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6265836918016326200147633 4699377688512244650110725)
                    ·
                      refine ⟨881133316596045871895761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4699377688512244650110725 881133316596045871895761)
                      ·
                        rfl

theorem cell23_1716001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1716001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716001 prefixEnd_1716001 := by exact prefixLift 1716001
  have htrace : WordTrace (prefixWord ++ tailWord_1716001) baseStart_1716001 baseEnd_1716001 := by
    simpa [prefixWord, tailWord_1716001, baseEnd_1716001] using wordTrace_append hprefix tailTrace_1716001
  have hstable : (prefixWord ++ tailWord_1716001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716001).length < 2 ^ (prefixWord ++ tailWord_1716001).sum := by decide
  have hdescent : baseEnd_1716001 < baseStart_1716001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716008 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1716008 : Nat := 118140960795 + 1716008 * 2 ^ 59
def prefixEnd_1716008 : Nat := 4983230072969 + 3 ^ 40 * 1716008 * 2
def baseEnd_1716008 : Nat := 881136910960627344508229

theorem tailTrace_1716008 : CollatzResearch.WordTrace tailWord_1716008 prefixEnd_1716008 881136910960627344508229 := by
  unfold tailWord_1716008
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293976783601780839474339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41725302378135707785965785 31293976783601780839474339)
  ·
    refine ⟨46940965175402671259211509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31293976783601780839474339 46940965175402671259211509)
    ·
      refine ⟨4400715485194000430551079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46940965175402671259211509 4400715485194000430551079)
      ·
        refine ⟨6601073227791000645826619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400715485194000430551079 6601073227791000645826619)
        ·
          refine ⟨9901609841686500968739929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601073227791000645826619 9901609841686500968739929)
          ·
            refine ⟨7426207381264875726554947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9901609841686500968739929 7426207381264875726554947)
            ·
              refine ⟨11139311071897313589832421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426207381264875726554947 11139311071897313589832421)
              ·
                refine ⟨2088620825980746298093579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11139311071897313589832421 2088620825980746298093579)
                ·
                  refine ⟨3132931238971119447140369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088620825980746298093579 3132931238971119447140369)
                  ·
                    refine ⟨2349698429228339585355277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3132931238971119447140369 2349698429228339585355277)
                    ·
                      refine ⟨881136910960627344508229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2349698429228339585355277 881136910960627344508229)
                      ·
                        rfl

theorem cell23_1716008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1716008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716008 prefixEnd_1716008 := by exact prefixLift 1716008
  have htrace : WordTrace (prefixWord ++ tailWord_1716008) baseStart_1716008 baseEnd_1716008 := by
    simpa [prefixWord, tailWord_1716008, baseEnd_1716008] using wordTrace_append hprefix tailTrace_1716008
  have hstable : (prefixWord ++ tailWord_1716008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716008).length < 2 ^ (prefixWord ++ tailWord_1716008).sum := by decide
  have hdescent : baseEnd_1716008 < baseStart_1716008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716055 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1716055 : Nat := 118140960795 + 1716055 * 2 ^ 59
def prefixEnd_1716055 : Nat := 4983230072969 + 3 ^ 40 * 1716055 * 2
def baseEnd_1716055 : Nat := 881161044551388660620513

theorem tailTrace_1716055 : CollatzResearch.WordTrace tailWord_1716055 prefixEnd_1716055 881161044551388660620513 := by
  unfold tailWord_1716055
  simp only [CollatzResearch.WordTrace]
  refine ⟨62589667798033288705909619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41726445198688859137273079 62589667798033288705909619)
  ·
    refine ⟨93884501697049933058864429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62589667798033288705909619 93884501697049933058864429)
    ·
      refine ⟨35206688136393724897074161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93884501697049933058864429 35206688136393724897074161)
      ·
        refine ⟨26405016102295293672805621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35206688136393724897074161 26405016102295293672805621)
        ·
          refine ⟨2475470259590183781825527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26405016102295293672805621 2475470259590183781825527)
          ·
            refine ⟨3713205389385275672738291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475470259590183781825527 3713205389385275672738291)
            ·
              refine ⟨5569808084077913509107437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713205389385275672738291 5569808084077913509107437)
              ·
                refine ⟨2088678031529217565915289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5569808084077913509107437 2088678031529217565915289)
                ·
                  refine ⟨1566508523646913174436467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088678031529217565915289 1566508523646913174436467)
                  ·
                    refine ⟨2349762785470369761654701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1566508523646913174436467 2349762785470369761654701)
                    ·
                      refine ⟨881161044551388660620513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2349762785470369761654701 881161044551388660620513)
                      ·
                        rfl

theorem cell23_1716055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1716055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716055 prefixEnd_1716055 := by exact prefixLift 1716055
  have htrace : WordTrace (prefixWord ++ tailWord_1716055) baseStart_1716055 baseEnd_1716055 := by
    simpa [prefixWord, tailWord_1716055, baseEnd_1716055] using wordTrace_append hprefix tailTrace_1716055
  have hstable : (prefixWord ++ tailWord_1716055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716055).length < 2 ^ (prefixWord ++ tailWord_1716055).sum := by decide
  have hdescent : baseEnd_1716055 < baseStart_1716055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716135 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 5]
def baseStart_1716135 : Nat := 118140960795 + 1716135 * 2 ^ 59
def prefixEnd_1716135 : Nat := 4983230072969 + 3 ^ 40 * 1716135 * 2
def baseEnd_1716135 : Nat := 97911347000416483068905

theorem tailTrace_1716135 : CollatzResearch.WordTrace tailWord_1716135 prefixEnd_1716135 97911347000416483068905 := by
  unfold tailWord_1716135
  simp only [CollatzResearch.WordTrace]
  refine ⟨62592585637743462368821859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41728390425162308245881239 62592585637743462368821859)
  ·
    refine ⟨93888878456615193553232789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62592585637743462368821859 93888878456615193553232789)
    ·
      refine ⟨4401041177653837197807787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93888878456615193553232789 4401041177653837197807787)
      ·
        refine ⟨6601561766480755796711681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401041177653837197807787 6601561766480755796711681)
        ·
          refine ⟨4951171324860566847533761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6601561766480755796711681 4951171324860566847533761)
          ·
            refine ⟨3713378493645425135650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4951171324860566847533761 3713378493645425135650321)
            ·
              refine ⟨2785033870234068851737741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713378493645425135650321 2785033870234068851737741)
              ·
                refine ⟨1044387701337775819401653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2785033870234068851737741 1044387701337775819401653)
                ·
                  refine ⟨97911347000416483068905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1044387701337775819401653 97911347000416483068905)
                  ·
                    rfl

theorem cell23_1716135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 5].length) (baseStart_1716135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716135 prefixEnd_1716135 := by exact prefixLift 1716135
  have htrace : WordTrace (prefixWord ++ tailWord_1716135) baseStart_1716135 baseEnd_1716135 := by
    simpa [prefixWord, tailWord_1716135, baseEnd_1716135] using wordTrace_append hprefix tailTrace_1716135
  have hstable : (prefixWord ++ tailWord_1716135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716135).length < 2 ^ (prefixWord ++ tailWord_1716135).sum := by decide
  have hdescent : baseEnd_1716135 < baseStart_1716135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716144 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_1716144 : Nat := 118140960795 + 1716144 * 2 ^ 59
def prefixEnd_1716144 : Nat := 4983230072969 + 3 ^ 40 * 1716144 * 2
def baseEnd_1716144 : Nat := 293735581443212937469201

theorem tailTrace_1716144 : CollatzResearch.WordTrace tailWord_1716144 prefixEnd_1716144 293735581443212937469201 := by
  unfold tailWord_1716144
  simp only [CollatzResearch.WordTrace]
  refine ⟨31296456947355428452949743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41728609263140571270599657 31296456947355428452949743)
  ·
    refine ⟨46944685421033142679424615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31296456947355428452949743 46944685421033142679424615)
    ·
      refine ⟨70417028131549714019136923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46944685421033142679424615 70417028131549714019136923)
      ·
        refine ⟨105625542197324571028705385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70417028131549714019136923 105625542197324571028705385)
        ·
          refine ⟨79219156647993428271529039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105625542197324571028705385 79219156647993428271529039)
          ·
            refine ⟨118828734971990142407293559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79219156647993428271529039 118828734971990142407293559)
            ·
              refine ⟨178243102457985213610940339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118828734971990142407293559 178243102457985213610940339)
              ·
                refine ⟨267364653686977820416410509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178243102457985213610940339 267364653686977820416410509)
                ·
                  refine ⟨100261745132616682656153941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267364653686977820416410509 100261745132616682656153941)
                  ·
                    refine ⟨293735581443212937469201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 100261745132616682656153941 293735581443212937469201)
                    ·
                      rfl

theorem cell23_1716144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_1716144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716144 prefixEnd_1716144 := by exact prefixLift 1716144
  have htrace : WordTrace (prefixWord ++ tailWord_1716144) baseStart_1716144 baseEnd_1716144 := by
    simpa [prefixWord, tailWord_1716144, baseEnd_1716144] using wordTrace_append hprefix tailTrace_1716144
  have hstable : (prefixWord ++ tailWord_1716144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716144).length < 2 ^ (prefixWord ++ tailWord_1716144).sum := by decide
  have hdescent : baseEnd_1716144 < baseStart_1716144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716151 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1716151 : Nat := 118140960795 + 1716151 * 2 ^ 59
def prefixEnd_1716151 : Nat := 4983230072969 + 3 ^ 40 * 1716151 * 2
def baseEnd_1716151 : Nat := 881210338694220285020071

theorem tailTrace_1716151 : CollatzResearch.WordTrace tailWord_1716151 prefixEnd_1716151 881210338694220285020071 := by
  unfold tailWord_1716151
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593169205685497101404307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41728779470456998067602871 62593169205685497101404307)
  ·
    refine ⟨93889753808528245652106461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62593169205685497101404307 93889753808528245652106461)
    ·
      refine ⟨35208657678198092119539923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93889753808528245652106461 35208657678198092119539923)
      ·
        refine ⟨52812986517297138179309885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35208657678198092119539923 52812986517297138179309885)
        ·
          refine ⟨19804869943986426817241207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52812986517297138179309885 19804869943986426817241207)
          ·
            refine ⟨29707304915979640225861811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19804869943986426817241207 29707304915979640225861811)
            ·
              refine ⟨44560957373969460338792717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29707304915979640225861811 44560957373969460338792717)
              ·
                refine ⟨16710359015238547627047269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44560957373969460338792717 16710359015238547627047269)
                ·
                  refine ⟨3133192315357227680071363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16710359015238547627047269 3133192315357227680071363)
                  ·
                    refine ⟨4699788473035841520107045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3133192315357227680071363 4699788473035841520107045)
                    ·
                      refine ⟨881210338694220285020071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4699788473035841520107045 881210338694220285020071)
                      ·
                        rfl

theorem cell23_1716151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1716151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716151 prefixEnd_1716151 := by exact prefixLift 1716151
  have htrace : WordTrace (prefixWord ++ tailWord_1716151) baseStart_1716151 baseEnd_1716151 := by
    simpa [prefixWord, tailWord_1716151, baseEnd_1716151] using wordTrace_append hprefix tailTrace_1716151
  have hstable : (prefixWord ++ tailWord_1716151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716151).length < 2 ^ (prefixWord ++ tailWord_1716151).sum := by decide
  have hdescent : baseEnd_1716151 < baseStart_1716151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716171 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3]
def baseStart_1716171 : Nat := 118140960795 + 1716171 * 2 ^ 59
def prefixEnd_1716171 : Nat := 4983230072969 + 3 ^ 40 * 1716171 * 2
def baseEnd_1716171 : Nat := 881220608307310206769979

theorem tailTrace_1716171 : CollatzResearch.WordTrace tailWord_1716171 prefixEnd_1716171 881220608307310206769979 := by
  unfold tailWord_1716171
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593898665613040517132367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41729265777075360344754911 62593898665613040517132367)
  ·
    refine ⟨93890847998419560775698551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62593898665613040517132367 93890847998419560775698551)
    ·
      refine ⟨140836271997629341163547827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93890847998419560775698551 140836271997629341163547827)
      ·
        refine ⟨211254407996444011745321741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140836271997629341163547827 211254407996444011745321741)
        ·
          refine ⟨79220402998666504404495653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211254407996444011745321741 79220402998666504404495653)
          ·
            refine ⟨14853825562249969575842935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79220402998666504404495653 14853825562249969575842935)
            ·
              refine ⟨22280738343374954363764403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14853825562249969575842935 22280738343374954363764403)
              ·
                refine ⟨33421107515062431545646605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22280738343374954363764403 33421107515062431545646605)
                ·
                  refine ⟨12532915318148411829617477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33421107515062431545646605 12532915318148411829617477)
                  ·
                    refine ⟨2349921622152827218053277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12532915318148411829617477 2349921622152827218053277)
                    ·
                      refine ⟨881220608307310206769979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2349921622152827218053277 881220608307310206769979)
                      ·
                        rfl

theorem cell23_1716171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3].length) (baseStart_1716171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716171 prefixEnd_1716171 := by exact prefixLift 1716171
  have htrace : WordTrace (prefixWord ++ tailWord_1716171) baseStart_1716171 baseEnd_1716171 := by
    simpa [prefixWord, tailWord_1716171, baseEnd_1716171] using wordTrace_append hprefix tailTrace_1716171
  have hstable : (prefixWord ++ tailWord_1716171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716171).length < 2 ^ (prefixWord ++ tailWord_1716171).sum := by decide
  have hdescent : baseEnd_1716171 < baseStart_1716171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716191 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 8]
def baseStart_1716191 : Nat := 118140960795 + 1716191 * 2 ^ 59
def prefixEnd_1716191 : Nat := 4983230072969 + 3 ^ 40 * 1716191 * 2
def baseEnd_1716191 : Nat := 97914541991155569835543

theorem tailTrace_1716191 : CollatzResearch.WordTrace tailWord_1716191 prefixEnd_1716191 97914541991155569835543 := by
  unfold tailWord_1716191
  simp only [CollatzResearch.WordTrace]
  refine ⟨62594628125540583932860427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41729752083693722621906951 62594628125540583932860427)
  ·
    refine ⟨93891942188310875899290641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62594628125540583932860427 93891942188310875899290641)
    ·
      refine ⟨70418956641233156924467981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93891942188310875899290641 70418956641233156924467981)
      ·
        refine ⟨26407108740462433846675493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70418956641233156924467981 26407108740462433846675493)
        ·
          refine ⟨4951332888836706346251655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26407108740462433846675493 4951332888836706346251655)
          ·
            refine ⟨7426999333255059519377483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951332888836706346251655 7426999333255059519377483)
            ·
              refine ⟨11140498999882589279066225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426999333255059519377483 11140498999882589279066225)
              ·
                refine ⟨8355374249911941959299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11140498999882589279066225 8355374249911941959299669)
                ·
                  refine ⟨97914541991155569835543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8355374249911941959299669 97914541991155569835543)
                  ·
                    rfl

theorem cell23_1716191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 8].length) (baseStart_1716191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716191 prefixEnd_1716191 := by exact prefixLift 1716191
  have htrace : WordTrace (prefixWord ++ tailWord_1716191) baseStart_1716191 baseEnd_1716191 := by
    simpa [prefixWord, tailWord_1716191, baseEnd_1716191] using wordTrace_append hprefix tailTrace_1716191
  have hstable : (prefixWord ++ tailWord_1716191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716191).length < 2 ^ (prefixWord ++ tailWord_1716191).sum := by decide
  have hdescent : baseEnd_1716191 < baseStart_1716191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716238 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_1716238 : Nat := 118140960795 + 1716238 * 2 ^ 59
def prefixEnd_1716238 : Nat := 4983230072969 + 3 ^ 40 * 1716238 * 2
def baseEnd_1716238 : Nat := 293751670503720481544057

theorem tailTrace_1716238 : CollatzResearch.WordTrace tailWord_1716238 prefixEnd_1716238 293751670503720481544057 := by
  unfold tailWord_1716238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7824542794546288869977671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41730894904246873973214245 7824542794546288869977671)
  ·
    refine ⟨11736814191819433304966507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7824542794546288869977671 11736814191819433304966507)
    ·
      refine ⟨17605221287729149957449761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11736814191819433304966507 17605221287729149957449761)
      ·
        refine ⟨13203915965796862468087321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17605221287729149957449761 13203915965796862468087321)
        ·
          refine ⟨9902936974347646851065491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203915965796862468087321 9902936974347646851065491)
          ·
            refine ⟨14854405461521470276598237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9902936974347646851065491 14854405461521470276598237)
            ·
              refine ⟨5570402048070551353724339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14854405461521470276598237 5570402048070551353724339)
              ·
                refine ⟨8355603072105827030586509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570402048070551353724339 8355603072105827030586509)
                ·
                  refine ⟨3133351152039685136469941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8355603072105827030586509 3133351152039685136469941)
                  ·
                    refine ⟨293751670503720481544057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3133351152039685136469941 293751670503720481544057)
                    ·
                      rfl

theorem cell23_1716238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_1716238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716238 prefixEnd_1716238 := by exact prefixLift 1716238
  have htrace : WordTrace (prefixWord ++ tailWord_1716238) baseStart_1716238 baseEnd_1716238 := by
    simpa [prefixWord, tailWord_1716238, baseEnd_1716238] using wordTrace_append hprefix tailTrace_1716238
  have hstable : (prefixWord ++ tailWord_1716238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716238).length < 2 ^ (prefixWord ++ tailWord_1716238).sum := by decide
  have hdescent : baseEnd_1716238 < baseStart_1716238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716255 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 1, 5]
def baseStart_1716255 : Nat := 118140960795 + 1716255 * 2 ^ 59
def prefixEnd_1716255 : Nat := 4983230072969 + 3 ^ 40 * 1716255 * 2
def baseEnd_1716255 : Nat := 293754580227429292706531

theorem tailTrace_1716255 : CollatzResearch.WordTrace tailWord_1716255 prefixEnd_1716255 293754580227429292706531 := by
  unfold tailWord_1716255
  simp only [CollatzResearch.WordTrace]
  refine ⟨62596962397308722863190219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41731308264872481908793479 62596962397308722863190219)
  ·
    refine ⟨93895443595963084294785329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62596962397308722863190219 93895443595963084294785329)
    ·
      refine ⟨70421582696972313221088997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93895443595963084294785329 70421582696972313221088997)
      ·
        refine ⟨13204046755682308728954187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70421582696972313221088997 13204046755682308728954187)
        ·
          refine ⟨19806070133523463093431281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204046755682308728954187 19806070133523463093431281)
          ·
            refine ⟨14854552600142597320073461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19806070133523463093431281 14854552600142597320073461)
            ·
              refine ⟨1392614306263368498756887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14854552600142597320073461 1392614306263368498756887)
              ·
                refine ⟨2088921459395052748135331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392614306263368498756887 2088921459395052748135331)
                ·
                  refine ⟨3133382189092579122202997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088921459395052748135331 3133382189092579122202997)
                  ·
                    refine ⟨293754580227429292706531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3133382189092579122202997 293754580227429292706531)
                    ·
                      rfl

theorem cell23_1716255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_1716255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716255 prefixEnd_1716255 := by exact prefixLift 1716255
  have htrace : WordTrace (prefixWord ++ tailWord_1716255) baseStart_1716255 baseEnd_1716255 := by
    simpa [prefixWord, tailWord_1716255, baseEnd_1716255] using wordTrace_append hprefix tailTrace_1716255
  have hstable : (prefixWord ++ tailWord_1716255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716255).length < 2 ^ (prefixWord ++ tailWord_1716255).sum := by decide
  have hdescent : baseEnd_1716255 < baseStart_1716255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716263 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1716263 : Nat := 118140960795 + 1716263 * 2 ^ 59
def prefixEnd_1716263 : Nat := 4983230072969 + 3 ^ 40 * 1716263 * 2
def baseEnd_1716263 : Nat := 293755949509174615606519

theorem tailTrace_1716263 : CollatzResearch.WordTrace tailWord_1716263 prefixEnd_1716263 293755949509174615606519 := by
  unfold tailWord_1716263
  simp only [CollatzResearch.WordTrace]
  refine ⟨62597254181279740229481443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41731502787519826819654295 62597254181279740229481443)
  ·
    refine ⟨93895881271919610344222165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62597254181279740229481443 93895881271919610344222165)
    ·
      refine ⟨2200684717310615867442707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 93895881271919610344222165 2200684717310615867442707)
      ·
        refine ⟨3301027075965923801164061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200684717310615867442707 3301027075965923801164061)
        ·
          refine ⟨1237885153487221425436523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3301027075965923801164061 1237885153487221425436523)
          ·
            refine ⟨1856827730230832138154785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237885153487221425436523 1856827730230832138154785)
            ·
              refine ⟨1392620797673124103616089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856827730230832138154785 1392620797673124103616089)
              ·
                refine ⟨1044465598254843077712067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392620797673124103616089 1044465598254843077712067)
                ·
                  refine ⟨1566698397382264616568101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044465598254843077712067 1566698397382264616568101)
                  ·
                    refine ⟨293755949509174615606519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566698397382264616568101 293755949509174615606519)
                    ·
                      rfl

theorem cell23_1716263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1716263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716263 prefixEnd_1716263 := by exact prefixLift 1716263
  have htrace : WordTrace (prefixWord ++ tailWord_1716263) baseStart_1716263 baseEnd_1716263 := by
    simpa [prefixWord, tailWord_1716263, baseEnd_1716263] using wordTrace_append hprefix tailTrace_1716263
  have hstable : (prefixWord ++ tailWord_1716263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716263).length < 2 ^ (prefixWord ++ tailWord_1716263).sum := by decide
  have hdescent : baseEnd_1716263 < baseStart_1716263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716271 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_1716271 : Nat := 118140960795 + 1716271 * 2 ^ 59
def prefixEnd_1716271 : Nat := 4983230072969 + 3 ^ 40 * 1716271 * 2
def baseEnd_1716271 : Nat := 881271956372759815519519

theorem tailTrace_1716271 : CollatzResearch.WordTrace tailWord_1716271 prefixEnd_1716271 881271956372759815519519 := by
  unfold tailWord_1716271
  simp only [CollatzResearch.WordTrace]
  refine ⟨62597545965250757595772667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41731697310167171730515111 62597545965250757595772667)
  ·
    refine ⟨93896318947876136393659001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62597545965250757595772667 93896318947876136393659001)
    ·
      refine ⟨70422239210907102295244251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93896318947876136393659001 70422239210907102295244251)
      ·
        refine ⟨105633358816360653442866377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70422239210907102295244251 105633358816360653442866377)
        ·
          refine ⟨79225019112270490082149783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105633358816360653442866377 79225019112270490082149783)
          ·
            refine ⟨118837528668405735123224675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79225019112270490082149783 118837528668405735123224675)
            ·
              refine ⟨178256293002608602684837013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118837528668405735123224675 178256293002608602684837013)
              ·
                refine ⟨8355763734497278250851735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178256293002608602684837013 8355763734497278250851735)
                ·
                  refine ⟨12533645601745917376277603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8355763734497278250851735 12533645601745917376277603)
                  ·
                    refine ⟨18800468402618876064416405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12533645601745917376277603 18800468402618876064416405)
                    ·
                      refine ⟨881271956372759815519519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18800468402618876064416405 881271956372759815519519)
                      ·
                        rfl

theorem cell23_1716271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_1716271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716271 prefixEnd_1716271 := by exact prefixLift 1716271
  have htrace : WordTrace (prefixWord ++ tailWord_1716271) baseStart_1716271 baseEnd_1716271 := by
    simpa [prefixWord, tailWord_1716271, baseEnd_1716271] using wordTrace_append hprefix tailTrace_1716271
  have hstable : (prefixWord ++ tailWord_1716271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716271).length < 2 ^ (prefixWord ++ tailWord_1716271).sum := by decide
  have hdescent : baseEnd_1716271 < baseStart_1716271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716285 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1716285 : Nat := 118140960795 + 1716285 * 2 ^ 59
def prefixEnd_1716285 : Nat := 4983230072969 + 3 ^ 40 * 1716285 * 2
def baseEnd_1716285 : Nat := 293759715033974253581485

theorem tailTrace_1716285 : CollatzResearch.WordTrace tailWord_1716285 prefixEnd_1716285 293759715033974253581485 := by
  unfold tailWord_1716285
  simp only [CollatzResearch.WordTrace]
  refine ⟨62598056587200037986782309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41732037724800025324521539 62598056587200037986782309)
  ·
    refine ⟨11737135610100007122521683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62598056587200037986782309 11737135610100007122521683)
    ·
      refine ⟨17605703415150010683782525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11737135610100007122521683 17605703415150010683782525)
      ·
        refine ⟨6602138780681254006418447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17605703415150010683782525 6602138780681254006418447)
        ·
          refine ⟨9903208171021881009627671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602138780681254006418447 9903208171021881009627671)
          ·
            refine ⟨14854812256532821514441507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9903208171021881009627671 14854812256532821514441507)
            ·
              refine ⟨22282218384799232271662261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14854812256532821514441507 22282218384799232271662261)
              ·
                refine ⟨2088957973574928025468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22282218384799232271662261 2088957973574928025468337)
                ·
                  refine ⟨1566718480181196019101253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088957973574928025468337 1566718480181196019101253)
                  ·
                    refine ⟨293759715033974253581485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566718480181196019101253 293759715033974253581485)
                    ·
                      rfl

theorem cell23_1716285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1716285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716285 prefixEnd_1716285 := by exact prefixLift 1716285
  have htrace : WordTrace (prefixWord ++ tailWord_1716285) baseStart_1716285 baseEnd_1716285 := by
    simpa [prefixWord, tailWord_1716285, baseEnd_1716285] using wordTrace_append hprefix tailTrace_1716285
  have hstable : (prefixWord ++ tailWord_1716285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716285).length < 2 ^ (prefixWord ++ tailWord_1716285).sum := by decide
  have hdescent : baseEnd_1716285 < baseStart_1716285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716288 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1716288 : Nat := 118140960795 + 1716288 * 2 ^ 59
def prefixEnd_1716288 : Nat := 4983230072969 + 3 ^ 40 * 1716288 * 2
def baseEnd_1716288 : Nat := 881280685543886249006941

theorem tailTrace_1716288 : CollatzResearch.WordTrace tailWord_1716288 prefixEnd_1716288 881280685543886249006941 := by
  unfold tailWord_1716288
  simp only [CollatzResearch.WordTrace]
  refine ⟨31299083003094584749570759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41732110670792779666094345 31299083003094584749570759)
  ·
    refine ⟨46948624504641877124356139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31299083003094584749570759 46948624504641877124356139)
    ·
      refine ⟨70422936756962815686534209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46948624504641877124356139 70422936756962815686534209)
      ·
        refine ⟨52817202567722111764900657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70422936756962815686534209 52817202567722111764900657)
        ·
          refine ⟨39612901925791583823675493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52817202567722111764900657 39612901925791583823675493)
          ·
            refine ⟨7427419111085921966939155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39612901925791583823675493 7427419111085921966939155)
            ·
              refine ⟨11141128666628882950408733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427419111085921966939155 11141128666628882950408733)
              ·
                refine ⟨4177923249985831106403275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11141128666628882950408733 4177923249985831106403275)
                ·
                  refine ⟨6266884874978746659604913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177923249985831106403275 6266884874978746659604913)
                  ·
                    refine ⟨4700163656234059994703685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6266884874978746659604913 4700163656234059994703685)
                    ·
                      refine ⟨881280685543886249006941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4700163656234059994703685 881280685543886249006941)
                      ·
                        rfl

theorem cell23_1716288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1716288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716288 prefixEnd_1716288 := by exact prefixLift 1716288
  have htrace : WordTrace (prefixWord ++ tailWord_1716288) baseStart_1716288 baseEnd_1716288 := by
    simpa [prefixWord, tailWord_1716288, baseEnd_1716288] using wordTrace_append hprefix tailTrace_1716288
  have hstable : (prefixWord ++ tailWord_1716288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716288).length < 2 ^ (prefixWord ++ tailWord_1716288).sum := by decide
  have hdescent : baseEnd_1716288 < baseStart_1716288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716295 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_1716295 : Nat := 118140960795 + 1716295 * 2 ^ 59
def prefixEnd_1716295 : Nat := 4983230072969 + 3 ^ 40 * 1716295 * 2
def baseEnd_1716295 : Nat := 881284279908467721619409

theorem tailTrace_1716295 : CollatzResearch.WordTrace tailWord_1716295 prefixEnd_1716295 881284279908467721619409 := by
  unfold tailWord_1716295
  simp only [CollatzResearch.WordTrace]
  refine ⟨62598421317163809694646339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41732280878109206463097559 62598421317163809694646339)
  ·
    refine ⟨93897631975745714541969509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62598421317163809694646339 93897631975745714541969509)
    ·
      refine ⟨17605805995452321476619283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93897631975745714541969509 17605805995452321476619283)
      ·
        refine ⟨26408708993178482214928925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17605805995452321476619283 26408708993178482214928925)
        ·
          refine ⟨9903265872441930830598347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26408708993178482214928925 9903265872441930830598347)
          ·
            refine ⟨14854898808662896245897521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9903265872441930830598347 14854898808662896245897521)
            ·
              refine ⟨11141174106497172184423141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14854898808662896245897521 11141174106497172184423141)
              ·
                refine ⟨2088970144968219784579339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11141174106497172184423141 2088970144968219784579339)
                ·
                  refine ⟨3133455217452329676869009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088970144968219784579339 3133455217452329676869009)
                  ·
                    refine ⟨2350091413089247257651757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3133455217452329676869009 2350091413089247257651757)
                    ·
                      refine ⟨881284279908467721619409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350091413089247257651757 881284279908467721619409)
                      ·
                        rfl

theorem cell23_1716295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_1716295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716295 prefixEnd_1716295 := by exact prefixLift 1716295
  have htrace : WordTrace (prefixWord ++ tailWord_1716295) baseStart_1716295 baseEnd_1716295 := by
    simpa [prefixWord, tailWord_1716295, baseEnd_1716295] using wordTrace_append hprefix tailTrace_1716295
  have hstable : (prefixWord ++ tailWord_1716295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716295).length < 2 ^ (prefixWord ++ tailWord_1716295).sum := by decide
  have hdescent : baseEnd_1716295 < baseStart_1716295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716309 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1716309 : Nat := 118140960795 + 1716309 * 2 ^ 59
def prefixEnd_1716309 : Nat := 4983230072969 + 3 ^ 40 * 1716309 * 2
def baseEnd_1716309 : Nat := 881291468637630666844345

theorem tailTrace_1716309 : CollatzResearch.WordTrace tailWord_1716309 prefixEnd_1716309 881291468637630666844345 := by
  unfold tailWord_1716309
  simp only [CollatzResearch.WordTrace]
  refine ⟨62598931939113090085655981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41732621292742060057103987 62598931939113090085655981)
  ·
    refine ⟨23474599477167408782120993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62598931939113090085655981 23474599477167408782120993)
    ·
      refine ⟨17605949607875556586590745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23474599477167408782120993 17605949607875556586590745)
      ·
        refine ⟨13204462205906667439943059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17605949607875556586590745 13204462205906667439943059)
        ·
          refine ⟨19806693308860001159914589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13204462205906667439943059 19806693308860001159914589)
          ·
            refine ⟨7427509990822500434967971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19806693308860001159914589 7427509990822500434967971)
            ·
              refine ⟨11141264986233750652451957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427509990822500434967971 11141264986233750652451957)
              ·
                refine ⟨1044493592459414123667371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11141264986233750652451957 1044493592459414123667371)
                ·
                  refine ⟨1566740388689121185501057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044493592459414123667371 1566740388689121185501057)
                  ·
                    refine ⟨1175055291516840889125793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1566740388689121185501057 1175055291516840889125793)
                    ·
                      refine ⟨881291468637630666844345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175055291516840889125793 881291468637630666844345)
                      ·
                        rfl

theorem cell23_1716309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1716309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716309 prefixEnd_1716309 := by exact prefixLift 1716309
  have htrace : WordTrace (prefixWord ++ tailWord_1716309) baseStart_1716309 baseEnd_1716309 := by
    simpa [prefixWord, tailWord_1716309, baseEnd_1716309] using wordTrace_append hprefix tailTrace_1716309
  have hstable : (prefixWord ++ tailWord_1716309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716309).length < 2 ^ (prefixWord ++ tailWord_1716309).sum := by decide
  have hdescent : baseEnd_1716309 < baseStart_1716309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716312 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_1716312 : Nat := 118140960795 + 1716312 * 2 ^ 59
def prefixEnd_1716312 : Nat := 4983230072969 + 3 ^ 40 * 1716312 * 2
def baseEnd_1716312 : Nat := 881293009079594155106831

theorem tailTrace_1716312 : CollatzResearch.WordTrace tailWord_1716312 prefixEnd_1716312 881293009079594155106831 := by
  unfold tailWord_1716312
  simp only [CollatzResearch.WordTrace]
  refine ⟨31299520679051110799007595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41732694238734814398676793 31299520679051110799007595)
  ·
    refine ⟨46949281018576666198511393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31299520679051110799007595 46949281018576666198511393)
    ·
      refine ⟨35211960763932499648883545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46949281018576666198511393 35211960763932499648883545)
      ·
        refine ⟨26408970572949374736662659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35211960763932499648883545 26408970572949374736662659)
        ·
          refine ⟨39613455859424062104993989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26408970572949374736662659 39613455859424062104993989)
          ·
            refine ⟨7427522973642011644686373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39613455859424062104993989 7427522973642011644686373)
            ·
              refine ⟨1392660557557877183378695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7427522973642011644686373 1392660557557877183378695)
              ·
                refine ⟨2088990836336815775068043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392660557557877183378695 2088990836336815775068043)
                ·
                  refine ⟨3133486254505223662602065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088990836336815775068043 3133486254505223662602065)
                  ·
                    refine ⟨2350114690878917746951549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3133486254505223662602065 2350114690878917746951549)
                    ·
                      refine ⟨881293009079594155106831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350114690878917746951549 881293009079594155106831)
                      ·
                        rfl

theorem cell23_1716312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_1716312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716312 prefixEnd_1716312 := by exact prefixLift 1716312
  have htrace : WordTrace (prefixWord ++ tailWord_1716312) baseStart_1716312 baseEnd_1716312 := by
    simpa [prefixWord, tailWord_1716312, baseEnd_1716312] using wordTrace_append hprefix tailTrace_1716312
  have hstable : (prefixWord ++ tailWord_1716312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716312).length < 2 ^ (prefixWord ++ tailWord_1716312).sum := by decide
  have hdescent : baseEnd_1716312 < baseStart_1716312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716342 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1716342 : Nat := 118140960795 + 1716342 * 2 ^ 59
def prefixEnd_1716342 : Nat := 4983230072969 + 3 ^ 40 * 1716342 * 2
def baseEnd_1716342 : Nat := 881308413499229037731693

theorem tailTrace_1716342 : CollatzResearch.WordTrace tailWord_1716342 prefixEnd_1716342 881308413499229037731693 := by
  unfold tailWord_1716342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912508471749596045100455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41733423698662357814404853 3912508471749596045100455)
  ·
    refine ⟨5868762707624394067650683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3912508471749596045100455 5868762707624394067650683)
    ·
      refine ⟨8803144061436591101476025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5868762707624394067650683 8803144061436591101476025)
      ·
        refine ⟨6602358046077443326107019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8803144061436591101476025 6602358046077443326107019)
        ·
          refine ⟨9903537069116164989160529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602358046077443326107019 9903537069116164989160529)
          ·
            refine ⟨7427652801837123741870397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9903537069116164989160529 7427652801837123741870397)
            ·
              refine ⟨2785369800688921403201399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7427652801837123741870397 2785369800688921403201399)
              ·
                refine ⟨4178054701033382104802099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785369800688921403201399 4178054701033382104802099)
                ·
                  refine ⟨6267082051550073157203149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178054701033382104802099 6267082051550073157203149)
                  ·
                    refine ⟨2350155769331277433951181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6267082051550073157203149 2350155769331277433951181)
                    ·
                      refine ⟨881308413499229037731693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350155769331277433951181 881308413499229037731693)
                      ·
                        rfl

theorem cell23_1716342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1716342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716342 prefixEnd_1716342 := by exact prefixLift 1716342
  have htrace : WordTrace (prefixWord ++ tailWord_1716342) baseStart_1716342 baseEnd_1716342 := by
    simpa [prefixWord, tailWord_1716342, baseEnd_1716342] using wordTrace_append hprefix tailTrace_1716342
  have hstable : (prefixWord ++ tailWord_1716342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716342).length < 2 ^ (prefixWord ++ tailWord_1716342).sum := by decide
  have hdescent : baseEnd_1716342 < baseStart_1716342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716368 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1716368 : Nat := 118140960795 + 1716368 * 2 ^ 59
def prefixEnd_1716368 : Nat := 4983230072969 + 3 ^ 40 * 1716368 * 2
def baseEnd_1716368 : Nat := 881321763996245936006573

theorem tailTrace_1716368 : CollatzResearch.WordTrace tailWord_1716368 prefixEnd_1716368 881321763996245936006573 := by
  unfold tailWord_1716368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31300541922949671581026879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41734055897266228774702505 31300541922949671581026879)
  ·
    refine ⟨46950812884424507371540319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31300541922949671581026879 46950812884424507371540319)
    ·
      refine ⟨70426219326636761057310479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46950812884424507371540319 70426219326636761057310479)
      ·
        refine ⟨105639328989955141585965719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70426219326636761057310479 105639328989955141585965719)
        ·
          refine ⟨158458993484932712378948579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105639328989955141585965719 158458993484932712378948579)
          ·
            refine ⟨237688490227399068568422869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158458993484932712378948579 237688490227399068568422869)
            ·
              refine ⟨5570823989704665669572411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237688490227399068568422869 5570823989704665669572411)
              ·
                refine ⟨8356235984556998504358617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570823989704665669572411 8356235984556998504358617)
                ·
                  refine ⟨6267176988417748878268963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8356235984556998504358617 6267176988417748878268963)
                  ·
                    refine ⟨9400765482626623317403445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6267176988417748878268963 9400765482626623317403445)
                    ·
                      refine ⟨881321763996245936006573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9400765482626623317403445 881321763996245936006573)
                      ·
                        rfl

theorem cell23_1716368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1716368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716368 prefixEnd_1716368 := by exact prefixLift 1716368
  have htrace : WordTrace (prefixWord ++ tailWord_1716368) baseStart_1716368 baseEnd_1716368 := by
    simpa [prefixWord, tailWord_1716368, baseEnd_1716368] using wordTrace_append hprefix tailTrace_1716368
  have hstable : (prefixWord ++ tailWord_1716368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716368).length < 2 ^ (prefixWord ++ tailWord_1716368).sum := by decide
  have hdescent : baseEnd_1716368 < baseStart_1716368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716465 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_1716465 : Nat := 118140960795 + 1716465 * 2 ^ 59
def prefixEnd_1716465 : Nat := 4983230072969 + 3 ^ 40 * 1716465 * 2
def baseEnd_1716465 : Nat := 293790523873244018831209

theorem tailTrace_1716465 : CollatzResearch.WordTrace tailWord_1716465 prefixEnd_1716465 293790523873244018831209 := by
  unfold tailWord_1716465
  simp only [CollatzResearch.WordTrace]
  refine ⟨62604621726547928728334849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41736414484365285818889899 62604621726547928728334849)
  ·
    refine ⟨46953466294910946546251137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62604621726547928728334849 46953466294910946546251137)
    ·
      refine ⟨35215099721183209909688353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46953466294910946546251137 35215099721183209909688353)
      ·
        refine ⟨26411324790887407432266265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35215099721183209909688353 26411324790887407432266265)
        ·
          refine ⟨19808493593165555574199699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26411324790887407432266265 19808493593165555574199699)
          ·
            refine ⟨29712740389748333361299549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19808493593165555574199699 29712740389748333361299549)
            ·
              refine ⟨11142277646155625010487331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29712740389748333361299549 11142277646155625010487331)
              ·
                refine ⟨16713416469233437515730997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11142277646155625010487331 16713416469233437515730997)
                ·
                  refine ⟨1566882793990634767099781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16713416469233437515730997 1566882793990634767099781)
                  ·
                    refine ⟨293790523873244018831209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566882793990634767099781 293790523873244018831209)
                    ·
                      rfl

theorem cell23_1716465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_1716465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716465 prefixEnd_1716465 := by exact prefixLift 1716465
  have htrace : WordTrace (prefixWord ++ tailWord_1716465) baseStart_1716465 baseEnd_1716465 := by
    simpa [prefixWord, tailWord_1716465, baseEnd_1716465] using wordTrace_append hprefix tailTrace_1716465
  have hstable : (prefixWord ++ tailWord_1716465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716465).length < 2 ^ (prefixWord ++ tailWord_1716465).sum := by decide
  have hdescent : baseEnd_1716465 < baseStart_1716465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716575 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1716575 : Nat := 118140960795 + 1716575 * 2 ^ 59
def prefixEnd_1716575 : Nat := 4983230072969 + 3 ^ 40 * 1716575 * 2
def baseEnd_1716575 : Nat := 881428054491726626118121

theorem tailTrace_1716575 : CollatzResearch.WordTrace tailWord_1716575 prefixEnd_1716575 881428054491726626118121 := by
  unfold tailWord_1716575
  simp only [CollatzResearch.WordTrace]
  refine ⟨62608633756149417514839179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41739089170766278343226119 62608633756149417514839179)
  ·
    refine ⟨93912950634224126272258769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62608633756149417514839179 93912950634224126272258769)
    ·
      refine ⟨70434712975668094704194077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93912950634224126272258769 70434712975668094704194077)
      ·
        refine ⟨26413017365875535514072779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70434712975668094704194077 26413017365875535514072779)
        ·
          refine ⟨39619526048813303271109169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26413017365875535514072779 39619526048813303271109169)
          ·
            refine ⟨29714644536609977453331877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39619526048813303271109169 29714644536609977453331877)
            ·
              refine ⟨5571495850614370772499727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29714644536609977453331877 5571495850614370772499727)
              ·
                refine ⟨8357243775921556158749591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571495850614370772499727 8357243775921556158749591)
                ·
                  refine ⟨12535865663882334238124387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8357243775921556158749591 12535865663882334238124387)
                  ·
                    refine ⟨18803798495823501357186581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12535865663882334238124387 18803798495823501357186581)
                    ·
                      refine ⟨881428054491726626118121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18803798495823501357186581 881428054491726626118121)
                      ·
                        rfl

theorem cell23_1716575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1716575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716575 prefixEnd_1716575 := by exact prefixLift 1716575
  have htrace : WordTrace (prefixWord ++ tailWord_1716575) baseStart_1716575 baseEnd_1716575 := by
    simpa [prefixWord, tailWord_1716575, baseEnd_1716575] using wordTrace_append hprefix tailTrace_1716575
  have hstable : (prefixWord ++ tailWord_1716575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716575).length < 2 ^ (prefixWord ++ tailWord_1716575).sum := by decide
  have hdescent : baseEnd_1716575 < baseStart_1716575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716576 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 1, 5]
def baseStart_1716576 : Nat := 118140960795 + 1716576 * 2 ^ 59
def prefixEnd_1716576 : Nat := 4983230072969 + 3 ^ 40 * 1716576 * 2
def baseEnd_1716576 : Nat := 293809522657460374068539

theorem tailTrace_1716576 : CollatzResearch.WordTrace tailWord_1716576 prefixEnd_1716576 293809522657460374068539 := by
  unfold tailWord_1716576
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304335114572897342812791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41739113486097196457083721 31304335114572897342812791)
  ·
    refine ⟨46956502671859346014219187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31304335114572897342812791 46956502671859346014219187)
    ·
      refine ⟨70434754007789019021328781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46956502671859346014219187 70434754007789019021328781)
      ·
        refine ⟨26413032752920882132998293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70434754007789019021328781 26413032752920882132998293)
        ·
          refine ⟨1238110910293166349984295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26413032752920882132998293 1238110910293166349984295)
          ·
            refine ⟨1857166365439749524976443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238110910293166349984295 1857166365439749524976443)
            ·
              refine ⟨2785749548159624287464665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857166365439749524976443 2785749548159624287464665)
              ·
                refine ⟨2089312161119718215598499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785749548159624287464665 2089312161119718215598499)
                ·
                  refine ⟨3133968241679577323397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089312161119718215598499 3133968241679577323397749)
                  ·
                    refine ⟨293809522657460374068539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3133968241679577323397749 293809522657460374068539)
                    ·
                      rfl

theorem cell23_1716576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_1716576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716576 prefixEnd_1716576 := by exact prefixLift 1716576
  have htrace : WordTrace (prefixWord ++ tailWord_1716576) baseStart_1716576 baseEnd_1716576 := by
    simpa [prefixWord, tailWord_1716576, baseEnd_1716576] using wordTrace_append hprefix tailTrace_1716576
  have hstable : (prefixWord ++ tailWord_1716576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716576).length < 2 ^ (prefixWord ++ tailWord_1716576).sum := by decide
  have hdescent : baseEnd_1716576 < baseStart_1716576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716579 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1716579 : Nat := 118140960795 + 1716579 * 2 ^ 59
def prefixEnd_1716579 : Nat := 4983230072969 + 3 ^ 40 * 1716579 * 2
def baseEnd_1716579 : Nat := 881430108414344610468103

theorem tailTrace_1716579 : CollatzResearch.WordTrace tailWord_1716579 prefixEnd_1716579 881430108414344610468103 := by
  unfold tailWord_1716579
  simp only [CollatzResearch.WordTrace]
  refine ⟨62608779648134926197984791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41739186432089950798656527 62608779648134926197984791)
  ·
    refine ⟨93913169472202389296977187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62608779648134926197984791 93913169472202389296977187)
    ·
      refine ⟨140869754208303583945465781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93913169472202389296977187 140869754208303583945465781)
      ·
        refine ⟨13206539457028460994887417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140869754208303583945465781 13206539457028460994887417)
        ·
          refine ⟨9904904592771345746165563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13206539457028460994887417 9904904592771345746165563)
          ·
            refine ⟨14857356889157018619248345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904904592771345746165563 14857356889157018619248345)
            ·
              refine ⟨11143017666867763964436259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14857356889157018619248345 11143017666867763964436259)
              ·
                refine ⟨16714526500301645946654389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11143017666867763964436259 16714526500301645946654389)
                ·
                  refine ⟨1566986859403279307498849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16714526500301645946654389 1566986859403279307498849)
                  ·
                    refine ⟨1175240144552459480624137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1566986859403279307498849 1175240144552459480624137)
                    ·
                      refine ⟨881430108414344610468103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175240144552459480624137 881430108414344610468103)
                      ·
                        rfl

theorem cell23_1716579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1716579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716579 prefixEnd_1716579 := by exact prefixLift 1716579
  have htrace : WordTrace (prefixWord ++ tailWord_1716579) baseStart_1716579 baseEnd_1716579 := by
    simpa [prefixWord, tailWord_1716579, baseEnd_1716579] using wordTrace_append hprefix tailTrace_1716579
  have hstable : (prefixWord ++ tailWord_1716579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716579).length < 2 ^ (prefixWord ++ tailWord_1716579).sum := by decide
  have hdescent : baseEnd_1716579 < baseStart_1716579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716592 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_1716592 : Nat := 118140960795 + 1716592 * 2 ^ 59
def prefixEnd_1716592 : Nat := 4983230072969 + 3 ^ 40 * 1716592 * 2
def baseEnd_1716592 : Nat := 881436783662853059605543

theorem tailTrace_1716592 : CollatzResearch.WordTrace tailWord_1716592 prefixEnd_1716592 881436783662853059605543 := by
  unfold tailWord_1716592
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304626898543914709104015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41739502531391886278805353 31304626898543914709104015)
  ·
    refine ⟨46956940347815872063656023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31304626898543914709104015 46956940347815872063656023)
    ·
      refine ⟨70435410521723808095484035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46956940347815872063656023 70435410521723808095484035)
      ·
        refine ⟨105653115782585712143226053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70435410521723808095484035 105653115782585712143226053)
        ·
          refine ⟨19809959209234821026854885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105653115782585712143226053 19809959209234821026854885)
          ·
            refine ⟨3714367351731528942535291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19809959209234821026854885 3714367351731528942535291)
            ·
              refine ⟨5571551027597293413802937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714367351731528942535291 5571551027597293413802937)
              ·
                refine ⟨4178663270697970060352203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571551027597293413802937 4178663270697970060352203)
                ·
                  refine ⟨6267994906046955090528305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178663270697970060352203 6267994906046955090528305)
                  ·
                    refine ⟨4700996179535216317896229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6267994906046955090528305 4700996179535216317896229)
                    ·
                      refine ⟨881436783662853059605543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4700996179535216317896229 881436783662853059605543)
                      ·
                        rfl

theorem cell23_1716592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_1716592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716592 prefixEnd_1716592 := by exact prefixLift 1716592
  have htrace : WordTrace (prefixWord ++ tailWord_1716592) baseStart_1716592 baseEnd_1716592 := by
    simpa [prefixWord, tailWord_1716592, baseEnd_1716592] using wordTrace_append hprefix tailTrace_1716592
  have hstable : (prefixWord ++ tailWord_1716592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716592).length < 2 ^ (prefixWord ++ tailWord_1716592).sum := by decide
  have hdescent : baseEnd_1716592 < baseStart_1716592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716612 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1716612 : Nat := 118140960795 + 1716612 * 2 ^ 59
def prefixEnd_1716612 : Nat := 4983230072969 + 3 ^ 40 * 1716612 * 2
def baseEnd_1716612 : Nat := 881447053275942981355451

theorem tailTrace_1716612 : CollatzResearch.WordTrace tailWord_1716612 prefixEnd_1716612 881447053275942981355451 := by
  unfold tailWord_1716612
  simp only [CollatzResearch.WordTrace]
  refine ⟨31304991628507686416968045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41739988838010248555957393 31304991628507686416968045)
  ·
    refine ⟨11739371860690382406363017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31304991628507686416968045 11739371860690382406363017)
    ·
      refine ⟨8804528895517786804772263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11739371860690382406363017 8804528895517786804772263)
      ·
        refine ⟨13206793343276680207158395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804528895517786804772263 13206793343276680207158395)
        ·
          refine ⟨19810190014915020310737593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206793343276680207158395 19810190014915020310737593)
          ·
            refine ⟨14857642511186265233053195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810190014915020310737593 14857642511186265233053195)
            ·
              refine ⟨22286463766779397849579793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857642511186265233053195 22286463766779397849579793)
              ·
                refine ⟨16714847825084548387184845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22286463766779397849579793 16714847825084548387184845)
                ·
                  refine ⟨6268067934406705645194317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16714847825084548387184845 6268067934406705645194317)
                  ·
                    refine ⟨2350525475402514616947869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6268067934406705645194317 2350525475402514616947869)
                    ·
                      refine ⟨881447053275942981355451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350525475402514616947869 881447053275942981355451)
                      ·
                        rfl

theorem cell23_1716612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1716612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716612 prefixEnd_1716612 := by exact prefixLift 1716612
  have htrace : WordTrace (prefixWord ++ tailWord_1716612) baseStart_1716612 baseEnd_1716612 := by
    simpa [prefixWord, tailWord_1716612, baseEnd_1716612] using wordTrace_append hprefix tailTrace_1716612
  have hstable : (prefixWord ++ tailWord_1716612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716612).length < 2 ^ (prefixWord ++ tailWord_1716612).sum := by decide
  have hdescent : baseEnd_1716612 < baseStart_1716612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716615 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 9]
def baseStart_1716615 : Nat := 118140960795 + 1716615 * 2 ^ 59
def prefixEnd_1716615 : Nat := 4983230072969 + 3 ^ 40 * 1716615 * 2
def baseEnd_1716615 : Nat := 293816197905968823205979

theorem tailTrace_1716615 : CollatzResearch.WordTrace tailWord_1716615 prefixEnd_1716615 293816197905968823205979 := by
  unfold tailWord_1716615
  simp only [CollatzResearch.WordTrace]
  refine ⟨62610092676004504346295299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41740061784003002897530199 62610092676004504346295299)
  ·
    refine ⟨93915139014006756519442949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62610092676004504346295299 93915139014006756519442949)
    ·
      refine ⟨17609088565126266847395553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93915139014006756519442949 17609088565126266847395553)
      ·
        refine ⟨13206816423844700135546665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17609088565126266847395553 13206816423844700135546665)
        ·
          refine ⟨9905112317883525101659999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13206816423844700135546665 9905112317883525101659999)
          ·
            refine ⟨14857668476825287652489999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905112317883525101659999 14857668476825287652489999)
            ·
              refine ⟨22286502715237931478734999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857668476825287652489999 22286502715237931478734999)
              ·
                refine ⟨33429754072856897218102499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22286502715237931478734999 33429754072856897218102499)
                ·
                  refine ⟨50144631109285345827153749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33429754072856897218102499 50144631109285345827153749)
                  ·
                    refine ⟨293816197905968823205979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50144631109285345827153749 293816197905968823205979)
                    ·
                      rfl

theorem cell23_1716615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_1716615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716615 prefixEnd_1716615 := by exact prefixLift 1716615
  have htrace : WordTrace (prefixWord ++ tailWord_1716615) baseStart_1716615 baseEnd_1716615 := by
    simpa [prefixWord, tailWord_1716615, baseEnd_1716615] using wordTrace_append hprefix tailTrace_1716615
  have hstable : (prefixWord ++ tailWord_1716615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716615).length < 2 ^ (prefixWord ++ tailWord_1716615).sum := by decide
  have hdescent : baseEnd_1716615 < baseStart_1716615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716639 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 3, 3, 2]
def baseStart_1716639 : Nat := 118140960795 + 1716639 * 2 ^ 59
def prefixEnd_1716639 : Nat := 4983230072969 + 3 ^ 40 * 1716639 * 2
def baseEnd_1716639 : Nat := 881460917253614375717827

theorem tailTrace_1716639 : CollatzResearch.WordTrace tailWord_1716639 prefixEnd_1716639 881460917253614375717827 := by
  unfold tailWord_1716639
  simp only [CollatzResearch.WordTrace]
  refine ⟨62610968027917556445168971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41740645351945037630112647 62610968027917556445168971)
  ·
    refine ⟨93916452041876334667753457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62610968027917556445168971 93916452041876334667753457)
    ·
      refine ⟨70437339031407251000815093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93916452041876334667753457 70437339031407251000815093)
      ·
        refine ⟨6603500534194429781326415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70437339031407251000815093 6603500534194429781326415)
        ·
          refine ⟨9905250801291644671989623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603500534194429781326415 9905250801291644671989623)
          ·
            refine ⟨14857876201937467007984435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905250801291644671989623 14857876201937467007984435)
            ·
              refine ⟨22286814302906200511976653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14857876201937467007984435 22286814302906200511976653)
              ·
                refine ⟨8357555363589825191991245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22286814302906200511976653 8357555363589825191991245)
                ·
                  refine ⟨3134083261346184446996717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8357555363589825191991245 3134083261346184446996717)
                  ·
                    refine ⟨1175281223004819167623769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134083261346184446996717 1175281223004819167623769)
                    ·
                      refine ⟨881460917253614375717827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175281223004819167623769 881460917253614375717827)
                      ·
                        rfl

theorem cell23_1716639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_1716639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716639 prefixEnd_1716639 := by exact prefixLift 1716639
  have htrace : WordTrace (prefixWord ++ tailWord_1716639) baseStart_1716639 baseEnd_1716639 := by
    simpa [prefixWord, tailWord_1716639, baseEnd_1716639] using wordTrace_append hprefix tailTrace_1716639
  have hstable : (prefixWord ++ tailWord_1716639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716639).length < 2 ^ (prefixWord ++ tailWord_1716639).sum := by decide
  have hdescent : baseEnd_1716639 < baseStart_1716639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716642 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1716642 : Nat := 118140960795 + 1716642 * 2 ^ 59
def prefixEnd_1716642 : Nat := 4983230072969 + 3 ^ 40 * 1716642 * 2
def baseEnd_1716642 : Nat := 881462457695577863980313

theorem tailTrace_1716642 : CollatzResearch.WordTrace tailWord_1716642 prefixEnd_1716642 881462457695577863980313 := by
  unfold tailWord_1716642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652769361726671989382045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41740718297937791971685453 15652769361726671989382045)
  ·
    refine ⟨5869788510647501996018267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15652769361726671989382045 5869788510647501996018267)
    ·
      refine ⟨8804682765971252994027401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869788510647501996018267 8804682765971252994027401)
      ·
        refine ⟨6603512074478439745520551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8804682765971252994027401 6603512074478439745520551)
        ·
          refine ⟨9905268111717659618280827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603512074478439745520551 9905268111717659618280827)
          ·
            refine ⟨14857902167576489427421241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905268111717659618280827 14857902167576489427421241)
            ·
              refine ⟨11143426625682367070565931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14857902167576489427421241 11143426625682367070565931)
              ·
                refine ⟨16715139938523550605848897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11143426625682367070565931 16715139938523550605848897)
                ·
                  refine ⟨12536354953892662954386673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16715139938523550605848897 12536354953892662954386673)
                  ·
                    refine ⟨9402266215419497215790005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12536354953892662954386673 9402266215419497215790005)
                    ·
                      refine ⟨881462457695577863980313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9402266215419497215790005 881462457695577863980313)
                      ·
                        rfl

theorem cell23_1716642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1716642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716642 prefixEnd_1716642 := by exact prefixLift 1716642
  have htrace : WordTrace (prefixWord ++ tailWord_1716642) baseStart_1716642 baseEnd_1716642 := by
    simpa [prefixWord, tailWord_1716642, baseEnd_1716642] using wordTrace_append hprefix tailTrace_1716642
  have hstable : (prefixWord ++ tailWord_1716642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716642).length < 2 ^ (prefixWord ++ tailWord_1716642).sum := by decide
  have hdescent : baseEnd_1716642 < baseStart_1716642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716645 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_1716645 : Nat := 118140960795 + 1716645 * 2 ^ 59
def prefixEnd_1716645 : Nat := 4983230072969 + 3 ^ 40 * 1716645 * 2
def baseEnd_1716645 : Nat := 293821332712513784080933

theorem tailTrace_1716645 : CollatzResearch.WordTrace tailWord_1716645 prefixEnd_1716645 293821332712513784080933 := by
  unfold tailWord_1716645
  simp only [CollatzResearch.WordTrace]
  refine ⟨62611186865895819469887389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41740791243930546313258259 62611186865895819469887389)
  ·
    refine ⟨23479195074710932301207771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62611186865895819469887389 23479195074710932301207771)
    ·
      refine ⟨35218792612066398451811657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23479195074710932301207771 35218792612066398451811657)
      ·
        refine ⟨26414094459049798838858743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35218792612066398451811657 26414094459049798838858743)
        ·
          refine ⟨39621141688574698258288115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26414094459049798838858743 39621141688574698258288115)
          ·
            refine ⟨59431712532862047387432173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39621141688574698258288115 59431712532862047387432173)
            ·
              refine ⟨22286892199823267770287065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59431712532862047387432173 22286892199823267770287065)
              ·
                refine ⟨16715169149867450827715299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22286892199823267770287065 16715169149867450827715299)
                ·
                  refine ⟨25072753724801176241572949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16715169149867450827715299 25072753724801176241572949)
                  ·
                    refine ⟨293821332712513784080933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25072753724801176241572949 293821332712513784080933)
                    ·
                      rfl

theorem cell23_1716645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_1716645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716645 prefixEnd_1716645 := by exact prefixLift 1716645
  have htrace : WordTrace (prefixWord ++ tailWord_1716645) baseStart_1716645 baseEnd_1716645 := by
    simpa [prefixWord, tailWord_1716645, baseEnd_1716645] using wordTrace_append hprefix tailTrace_1716645
  have hstable : (prefixWord ++ tailWord_1716645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716645).length < 2 ^ (prefixWord ++ tailWord_1716645).sum := by decide
  have hdescent : baseEnd_1716645 < baseStart_1716645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716650 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1716650 : Nat := 118140960795 + 1716650 * 2 ^ 59
def prefixEnd_1716650 : Nat := 4983230072969 + 3 ^ 40 * 1716650 * 2
def baseEnd_1716650 : Nat := 881466565540813832680277

theorem tailTrace_1716650 : CollatzResearch.WordTrace tailWord_1716650 prefixEnd_1716650 881466565540813832680277 := by
  unfold tailWord_1716650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652842307719426330954851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41740912820585136882546269 15652842307719426330954851)
  ·
    refine ⟨23479263461579139496432277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15652842307719426330954851 23479263461579139496432277)
    ·
      refine ⟨1100590474761522163895263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23479263461579139496432277 1100590474761522163895263)
      ·
        refine ⟨1650885712142283245842895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100590474761522163895263 1650885712142283245842895)
        ·
          refine ⟨2476328568213424868764343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650885712142283245842895 2476328568213424868764343)
          ·
            refine ⟨3714492852320137303146515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476328568213424868764343 3714492852320137303146515)
            ·
              refine ⟨5571739278480205954719773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714492852320137303146515 5571739278480205954719773)
              ·
                refine ⟨2089402229430077233019915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571739278480205954719773 2089402229430077233019915)
                ·
                  refine ⟨3134103344145115849529873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089402229430077233019915 3134103344145115849529873)
                  ·
                    refine ⟨2350577508108836887147405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134103344145115849529873 2350577508108836887147405)
                    ·
                      refine ⟨881466565540813832680277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350577508108836887147405 881466565540813832680277)
                      ·
                        rfl

theorem cell23_1716650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1716650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716650 prefixEnd_1716650 := by exact prefixLift 1716650
  have htrace : WordTrace (prefixWord ++ tailWord_1716650) baseStart_1716650 baseEnd_1716650 := by
    simpa [prefixWord, tailWord_1716650, baseEnd_1716650] using wordTrace_append hprefix tailTrace_1716650
  have hstable : (prefixWord ++ tailWord_1716650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716650).length < 2 ^ (prefixWord ++ tailWord_1716650).sum := by decide
  have hdescent : baseEnd_1716650 < baseStart_1716650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716682 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1716682 : Nat := 118140960795 + 1716682 * 2 ^ 59
def prefixEnd_1716682 : Nat := 4983230072969 + 3 ^ 40 * 1716682 * 2
def baseEnd_1716682 : Nat := 881482996921757707480129

theorem tailTrace_1716682 : CollatzResearch.WordTrace tailWord_1716682 prefixEnd_1716682 881482996921757707480129 := by
  unfold tailWord_1716682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653134091690443697246075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41741690911174516525989533 15653134091690443697246075)
  ·
    refine ⟨23479701137535665545869113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15653134091690443697246075 23479701137535665545869113)
    ·
      refine ⟨17609775853151749159401835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23479701137535665545869113 17609775853151749159401835)
      ·
        refine ⟨26414663779727623739102753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17609775853151749159401835 26414663779727623739102753)
        ·
          refine ⟨19810997834795717804327065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26414663779727623739102753 19810997834795717804327065)
          ·
            refine ⟨14858248376096788353245299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810997834795717804327065 14858248376096788353245299)
            ·
              refine ⟨22287372564145182529867949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858248376096788353245299 22287372564145182529867949)
              ·
                refine ⟨8357764711554443448700481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22287372564145182529867949 8357764711554443448700481)
                ·
                  refine ⟨6268323533665832586525361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357764711554443448700481 6268323533665832586525361)
                  ·
                    refine ⟨4701242650249374439894021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6268323533665832586525361 4701242650249374439894021)
                    ·
                      refine ⟨881482996921757707480129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4701242650249374439894021 881482996921757707480129)
                      ·
                        rfl

theorem cell23_1716682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1716682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716682 prefixEnd_1716682 := by exact prefixLift 1716682
  have htrace : WordTrace (prefixWord ++ tailWord_1716682) baseStart_1716682 baseEnd_1716682 := by
    simpa [prefixWord, tailWord_1716682, baseEnd_1716682] using wordTrace_append hprefix tailTrace_1716682
  have hstable : (prefixWord ++ tailWord_1716682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716682).length < 2 ^ (prefixWord ++ tailWord_1716682).sum := by decide
  have hdescent : baseEnd_1716682 < baseStart_1716682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716690 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1716690 : Nat := 118140960795 + 1716690 * 2 ^ 59
def prefixEnd_1716690 : Nat := 4983230072969 + 3 ^ 40 * 1716690 * 2
def baseEnd_1716690 : Nat := 881487104766993676180093

theorem tailTrace_1716690 : CollatzResearch.WordTrace tailWord_1716690 prefixEnd_1716690 881487104766993676180093 := by
  unfold tailWord_1716690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653207037683198038818881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41741885433821861436850349 15653207037683198038818881)
  ·
    refine ⟨11739905278262398529114161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15653207037683198038818881 11739905278262398529114161)
    ·
      refine ⟨8804928958696798896835621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11739905278262398529114161 8804928958696798896835621)
      ·
        refine ⟨1650924179755649793156679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8804928958696798896835621 1650924179755649793156679)
        ·
          refine ⟨2476386269633474689735019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650924179755649793156679 2476386269633474689735019)
          ·
            refine ⟨3714579404450212034602529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476386269633474689735019 3714579404450212034602529)
            ·
              refine ⟨2785934553337659025951897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714579404450212034602529 2785934553337659025951897)
              ·
                refine ⟨2089450915003244269463923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785934553337659025951897 2089450915003244269463923)
                ·
                  refine ⟨3134176372504866404195885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089450915003244269463923 3134176372504866404195885)
                  ·
                    refine ⟨1175316139689324901573457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134176372504866404195885 1175316139689324901573457)
                    ·
                      refine ⟨881487104766993676180093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175316139689324901573457 881487104766993676180093)
                      ·
                        rfl

theorem cell23_1716690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1716690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716690 prefixEnd_1716690 := by exact prefixLift 1716690
  have htrace : WordTrace (prefixWord ++ tailWord_1716690) baseStart_1716690 baseEnd_1716690 := by
    simpa [prefixWord, tailWord_1716690, baseEnd_1716690] using wordTrace_append hprefix tailTrace_1716690
  have hstable : (prefixWord ++ tailWord_1716690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716690).length < 2 ^ (prefixWord ++ tailWord_1716690).sum := by decide
  have hdescent : baseEnd_1716690 < baseStart_1716690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716756 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1716756 : Nat := 118140960795 + 1716756 * 2 ^ 59
def prefixEnd_1716756 : Nat := 4983230072969 + 3 ^ 40 * 1716756 * 2
def baseEnd_1716756 : Nat := 293840331496730139318263

theorem tailTrace_1716756 : CollatzResearch.WordTrace tailWord_1716756 prefixEnd_1716756 293840331496730139318263 := by
  unfold tailWord_1716756
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307617684246842713589061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41743490245662456951452081 31307617684246842713589061)
  ·
    refine ⟨5870178315796283008797949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31307617684246842713589061 5870178315796283008797949)
    ·
      refine ⟨2201316868423606128299231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5870178315796283008797949 2201316868423606128299231)
      ·
        refine ⟨3301975302635409192448847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201316868423606128299231 3301975302635409192448847)
        ·
          refine ⟨4952962953953113788673271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301975302635409192448847 4952962953953113788673271)
          ·
            refine ⟨7429444430929670683009907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952962953953113788673271 7429444430929670683009907)
            ·
              refine ⟨11144166646394506024514861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429444430929670683009907 11144166646394506024514861)
              ·
                refine ⟨4179062492397939759193073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11144166646394506024514861 4179062492397939759193073)
                ·
                  refine ⟨3134296869298454819394805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179062492397939759193073 3134296869298454819394805)
                  ·
                    refine ⟨293840331496730139318263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3134296869298454819394805 293840331496730139318263)
                    ·
                      rfl

theorem cell23_1716756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1716756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716756 prefixEnd_1716756 := by exact prefixLift 1716756
  have htrace : WordTrace (prefixWord ++ tailWord_1716756) baseStart_1716756 baseEnd_1716756 := by
    simpa [prefixWord, tailWord_1716756, baseEnd_1716756] using wordTrace_append hprefix tailTrace_1716756
  have hstable : (prefixWord ++ tailWord_1716756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716756).length < 2 ^ (prefixWord ++ tailWord_1716756).sum := by decide
  have hdescent : baseEnd_1716756 < baseStart_1716756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716776 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1716776 : Nat := 118140960795 + 1716776 * 2 ^ 59
def prefixEnd_1716776 : Nat := 4983230072969 + 3 ^ 40 * 1716776 * 2
def baseEnd_1716776 : Nat := 881531264103280339704697

theorem tailTrace_1716776 : CollatzResearch.WordTrace tailWord_1716776 prefixEnd_1716776 881531264103280339704697 := by
  unfold tailWord_1716776
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307982414210614421453091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41743976552280819228604121 31307982414210614421453091)
  ·
    refine ⟨46961973621315921632179637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31307982414210614421453091 46961973621315921632179637)
    ·
      refine ⟨4402685026998367653016841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46961973621315921632179637 4402685026998367653016841)
      ·
        refine ⟨3302013770248775739762631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4402685026998367653016841 3302013770248775739762631)
        ·
          refine ⟨4953020655373163609643947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302013770248775739762631 4953020655373163609643947)
          ·
            refine ⟨7429530983059745414465921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953020655373163609643947 7429530983059745414465921)
            ·
              refine ⟨5572148237294809060849441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7429530983059745414465921 5572148237294809060849441)
              ·
                refine ⟨4179111177971106795637081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5572148237294809060849441 4179111177971106795637081)
                ·
                  refine ⟨3134333383478330096727811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179111177971106795637081 3134333383478330096727811)
                  ·
                    refine ⟨4701500075217495145091717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3134333383478330096727811 4701500075217495145091717)
                    ·
                      refine ⟨881531264103280339704697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4701500075217495145091717 881531264103280339704697)
                      ·
                        rfl

theorem cell23_1716776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1716776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716776 prefixEnd_1716776 := by exact prefixLift 1716776
  have htrace : WordTrace (prefixWord ++ tailWord_1716776) baseStart_1716776 baseEnd_1716776 := by
    simpa [prefixWord, tailWord_1716776, baseEnd_1716776] using wordTrace_append hprefix tailTrace_1716776
  have hstable : (prefixWord ++ tailWord_1716776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716776).length < 2 ^ (prefixWord ++ tailWord_1716776).sum := by decide
  have hdescent : baseEnd_1716776 < baseStart_1716776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716813 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1716813 : Nat := 118140960795 + 1716813 * 2 ^ 59
def prefixEnd_1716813 : Nat := 4983230072969 + 3 ^ 40 * 1716813 * 2
def baseEnd_1716813 : Nat := 881550262887496694942027

theorem tailTrace_1716813 : CollatzResearch.WordTrace tailWord_1716813 prefixEnd_1716813 881550262887496694942027 := by
  unfold tailWord_1716813
  simp only [CollatzResearch.WordTrace]
  refine ⟨62617314329287184162003093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41744876219524789441335395 62617314329287184162003093)
  ·
    refine ⟨2935186609185336757593895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62617314329287184162003093 2935186609185336757593895)
    ·
      refine ⟨4402779913778005136390843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2935186609185336757593895 4402779913778005136390843)
      ·
        refine ⟨6604169870667007704586265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402779913778005136390843 6604169870667007704586265)
        ·
          refine ⟨4953127403000255778439699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6604169870667007704586265 4953127403000255778439699)
          ·
            refine ⟨7429691104500383667659549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953127403000255778439699 7429691104500383667659549)
            ·
              refine ⟨2786134164187643875372331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429691104500383667659549 2786134164187643875372331)
              ·
                refine ⟨4179201246281465813058497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786134164187643875372331 4179201246281465813058497)
                ·
                  refine ⟨3134400934711099359793873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179201246281465813058497 3134400934711099359793873)
                  ·
                    refine ⟨2350800701033324519845405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134400934711099359793873 2350800701033324519845405)
                    ·
                      refine ⟨881550262887496694942027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350800701033324519845405 881550262887496694942027)
                      ·
                        rfl

theorem cell23_1716813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1716813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716813 prefixEnd_1716813 := by exact prefixLift 1716813
  have htrace : WordTrace (prefixWord ++ tailWord_1716813) baseStart_1716813 baseEnd_1716813 := by
    simpa [prefixWord, tailWord_1716813, baseEnd_1716813] using wordTrace_append hprefix tailTrace_1716813
  have hstable : (prefixWord ++ tailWord_1716813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716813).length < 2 ^ (prefixWord ++ tailWord_1716813).sum := by decide
  have hdescent : baseEnd_1716813 < baseStart_1716813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716836 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_1716836 : Nat := 118140960795 + 1716836 * 2 ^ 59
def prefixEnd_1716836 : Nat := 4983230072969 + 3 ^ 40 * 1716836 * 2
def baseEnd_1716836 : Nat := 881562072942550104954421

theorem tailTrace_1716836 : CollatzResearch.WordTrace tailWord_1716836 prefixEnd_1716836 881562072942550104954421 := by
  unfold tailWord_1716836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309076604101929545045181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41745435472135906060060241 31309076604101929545045181)
  ·
    refine ⟨11740903726538223579391943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31309076604101929545045181 11740903726538223579391943)
    ·
      refine ⟨17611355589807335369087915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11740903726538223579391943 17611355589807335369087915)
      ·
        refine ⟨26417033384711003053631873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17611355589807335369087915 26417033384711003053631873)
        ·
          refine ⟨19812775038533252290223905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26417033384711003053631873 19812775038533252290223905)
          ·
            refine ⟨14859581278899939217667929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19812775038533252290223905 14859581278899939217667929)
            ·
              refine ⟨11144685959174954413250947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14859581278899939217667929 11144685959174954413250947)
              ·
                refine ⟨16717028938762431619876421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144685959174954413250947 16717028938762431619876421)
                ·
                  refine ⟨3134442926017955928726829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16717028938762431619876421 3134442926017955928726829)
                  ·
                    refine ⟨1175416097256733473272561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134442926017955928726829 1175416097256733473272561)
                    ·
                      refine ⟨881562072942550104954421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175416097256733473272561 881562072942550104954421)
                      ·
                        rfl

theorem cell23_1716836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_1716836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716836 prefixEnd_1716836 := by exact prefixLift 1716836
  have htrace : WordTrace (prefixWord ++ tailWord_1716836) baseStart_1716836 baseEnd_1716836 := by
    simpa [prefixWord, tailWord_1716836, baseEnd_1716836] using wordTrace_append hprefix tailTrace_1716836
  have hstable : (prefixWord ++ tailWord_1716836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716836).length < 2 ^ (prefixWord ++ tailWord_1716836).sum := by decide
  have hdescent : baseEnd_1716836 < baseStart_1716836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716899 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1716899 : Nat := 118140960795 + 1716899 * 2 ^ 59
def prefixEnd_1716899 : Nat := 4983230072969 + 3 ^ 40 * 1716899 * 2
def baseEnd_1716899 : Nat := 881594422223783358466631

theorem tailTrace_1716899 : CollatzResearch.WordTrace tailWord_1716899 prefixEnd_1716899 881594422223783358466631 := by
  unfold tailWord_1716899
  simp only [CollatzResearch.WordTrace]
  refine ⟨62620451006975620849633751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41746967337983747233089167 62620451006975620849633751)
  ·
    refine ⟨93930676510463431274450627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62620451006975620849633751 93930676510463431274450627)
    ·
      refine ⟨140896014765695146911675941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93930676510463431274450627 140896014765695146911675941)
      ·
        refine ⟨26418002768567840045939239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140896014765695146911675941 26418002768567840045939239)
        ·
          refine ⟨39627004152851760068908859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26418002768567840045939239 39627004152851760068908859)
          ·
            refine ⟨59440506229277640103363289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39627004152851760068908859 59440506229277640103363289)
            ·
              refine ⟨44580379671958230077522467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59440506229277640103363289 44580379671958230077522467)
              ·
                refine ⟨66870569507937345116283701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44580379671958230077522467 66870569507937345116283701)
                ·
                  refine ⟨6269115891369126104651597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66870569507937345116283701 6269115891369126104651597)
                  ·
                    refine ⟨2350918459263422289244349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6269115891369126104651597 2350918459263422289244349)
                    ·
                      refine ⟨881594422223783358466631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2350918459263422289244349 881594422223783358466631)
                      ·
                        rfl

theorem cell23_1716899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1716899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716899 prefixEnd_1716899 := by exact prefixLift 1716899
  have htrace : WordTrace (prefixWord ++ tailWord_1716899) baseStart_1716899 baseEnd_1716899 := by
    simpa [prefixWord, tailWord_1716899, baseEnd_1716899] using wordTrace_append hprefix tailTrace_1716899
  have hstable : (prefixWord ++ tailWord_1716899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716899).length < 2 ^ (prefixWord ++ tailWord_1716899).sum := by decide
  have hdescent : baseEnd_1716899 < baseStart_1716899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716910 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1716910 : Nat := 118140960795 + 1716910 * 2 ^ 59
def prefixEnd_1716910 : Nat := 4983230072969 + 3 ^ 40 * 1716910 * 2
def baseEnd_1716910 : Nat := 293866690170327605143027

theorem tailTrace_1716910 : CollatzResearch.WordTrace tailWord_1716910 prefixEnd_1716910 293866690170327605143027 := by
  unfold tailWord_1716910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827606526241971216035523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41747234806623846485522789 7827606526241971216035523)
  ·
    refine ⟨11741409789362956824053285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7827606526241971216035523 11741409789362956824053285)
    ·
      refine ⟨2201514335505554404509991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11741409789362956824053285 2201514335505554404509991)
      ·
        refine ⟨3302271503258331606764987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201514335505554404509991 3302271503258331606764987)
        ·
          refine ⟨4953407254887497410147481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302271503258331606764987 4953407254887497410147481)
          ·
            refine ⟨3715055441165623057610611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4953407254887497410147481 3715055441165623057610611)
            ·
              refine ⟨5572583161748434586415917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715055441165623057610611 5572583161748434586415917)
              ·
                refine ⟨2089718685655662969905969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5572583161748434586415917 2089718685655662969905969)
                ·
                  refine ⟨1567289014241747227429477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2089718685655662969905969 1567289014241747227429477)
                  ·
                    refine ⟨293866690170327605143027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567289014241747227429477 293866690170327605143027)
                    ·
                      rfl

theorem cell23_1716910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1716910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716910 prefixEnd_1716910 := by exact prefixLift 1716910
  have htrace : WordTrace (prefixWord ++ tailWord_1716910) baseStart_1716910 baseEnd_1716910 := by
    simpa [prefixWord, tailWord_1716910, baseEnd_1716910] using wordTrace_append hprefix tailTrace_1716910
  have hstable : (prefixWord ++ tailWord_1716910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716910).length < 2 ^ (prefixWord ++ tailWord_1716910).sum := by decide
  have hdescent : baseEnd_1716910 < baseStart_1716910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716934 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1716934 : Nat := 118140960795 + 1716934 * 2 ^ 59
def prefixEnd_1716934 : Nat := 4983230072969 + 3 ^ 40 * 1716934 * 2
def baseEnd_1716934 : Nat := 881612394046690721528971

theorem tailTrace_1716934 : CollatzResearch.WordTrace tailWord_1716934 prefixEnd_1716934 881612394046690721528971 := by
  unfold tailWord_1716934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956928986307775682098683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41747818374565881218105237 1956928986307775682098683)
  ·
    refine ⟨2935393479461663523148025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956928986307775682098683 2935393479461663523148025)
    ·
      refine ⟨2201545109596247642361019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2935393479461663523148025 2201545109596247642361019)
      ·
        refine ⟨3302317664394371463541529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201545109596247642361019 3302317664394371463541529)
        ·
          refine ⟨2476738248295778597656147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3302317664394371463541529 2476738248295778597656147)
          ·
            refine ⟨3715107372443667896484221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476738248295778597656147 3715107372443667896484221)
            ·
              refine ⟨1393165264666375461181583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3715107372443667896484221 1393165264666375461181583)
              ·
                refine ⟨2089747896999563191772375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393165264666375461181583 2089747896999563191772375)
                ·
                  refine ⟨3134621845499344787658563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089747896999563191772375 3134621845499344787658563)
                  ·
                    refine ⟨4701932768249017181487845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3134621845499344787658563 4701932768249017181487845)
                    ·
                      refine ⟨881612394046690721528971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4701932768249017181487845 881612394046690721528971)
                      ·
                        rfl

theorem cell23_1716934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1716934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716934 prefixEnd_1716934 := by exact prefixLift 1716934
  have htrace : WordTrace (prefixWord ++ tailWord_1716934) baseStart_1716934 baseEnd_1716934 := by
    simpa [prefixWord, tailWord_1716934, baseEnd_1716934] using wordTrace_append hprefix tailTrace_1716934
  have hstable : (prefixWord ++ tailWord_1716934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716934).length < 2 ^ (prefixWord ++ tailWord_1716934).sum := by decide
  have hdescent : baseEnd_1716934 < baseStart_1716934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716969 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_1716969 : Nat := 118140960795 + 1716969 * 2 ^ 59
def prefixEnd_1716969 : Nat := 4983230072969 + 3 ^ 40 * 1716969 * 2
def baseEnd_1716969 : Nat := 881630365869598084591309

theorem tailTrace_1716969 : CollatzResearch.WordTrace tailWord_1716969 prefixEnd_1716969 881630365869598084591309 := by
  unfold tailWord_1716969
  simp only [CollatzResearch.WordTrace]
  refine ⟨62623004116722022804681961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41748669411148015203121307 62623004116722022804681961)
  ·
    refine ⟨46967253087541517103511471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62623004116722022804681961 46967253087541517103511471)
    ·
      refine ⟨70450879631312275655267207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46967253087541517103511471 70450879631312275655267207)
      ·
        refine ⟨105676319446968413482900811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70450879631312275655267207 105676319446968413482900811)
        ·
          refine ⟨158514479170452620224351217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105676319446968413482900811 158514479170452620224351217)
          ·
            refine ⟨118885859377839465168263413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158514479170452620224351217 118885859377839465168263413)
            ·
              refine ⟨11145549316672449859524695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118885859377839465168263413 11145549316672449859524695)
              ·
                refine ⟨16718323975008674789287043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145549316672449859524695 16718323975008674789287043)
                ·
                  refine ⟨25077485962513012183930565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16718323975008674789287043 25077485962513012183930565)
                  ·
                    refine ⟨4702028617971189784486981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25077485962513012183930565 4702028617971189784486981)
                    ·
                      refine ⟨881630365869598084591309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4702028617971189784486981 881630365869598084591309)
                      ·
                        rfl

theorem cell23_1716969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_1716969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716969 prefixEnd_1716969 := by exact prefixLift 1716969
  have htrace : WordTrace (prefixWord ++ tailWord_1716969) baseStart_1716969 baseEnd_1716969 := by
    simpa [prefixWord, tailWord_1716969, baseEnd_1716969] using wordTrace_append hprefix tailTrace_1716969
  have hstable : (prefixWord ++ tailWord_1716969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716969).length < 2 ^ (prefixWord ++ tailWord_1716969).sum := by decide
  have hdescent : baseEnd_1716969 < baseStart_1716969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716990 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1716990 : Nat := 118140960795 + 1716990 * 2 ^ 59
def prefixEnd_1716990 : Nat := 4983230072969 + 3 ^ 40 * 1716990 * 2
def baseEnd_1716990 : Nat := 881641148963342502428713

theorem tailTrace_1716990 : CollatzResearch.WordTrace tailWord_1716990 prefixEnd_1716990 881641148963342502428713 := by
  unfold tailWord_1716990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827971256205742923899553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41749180033097295594130949 7827971256205742923899553)
  ·
    refine ⟨5870978442154307192924665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7827971256205742923899553 5870978442154307192924665)
    ·
      refine ⟨4403233831615730394693499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5870978442154307192924665 4403233831615730394693499)
      ·
        refine ⟨6604850747423595592040249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403233831615730394693499 6604850747423595592040249)
        ·
          refine ⟨4953638060567696694030187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6604850747423595592040249 4953638060567696694030187)
          ·
            refine ⟨7430457090851545041045281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953638060567696694030187 7430457090851545041045281)
            ·
              refine ⟨5572842818138658780783961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7430457090851545041045281 5572842818138658780783961)
              ·
                refine ⟨4179632113603994085587971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5572842818138658780783961 4179632113603994085587971)
                ·
                  refine ⟨6269448170405991128381957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179632113603994085587971 6269448170405991128381957)
                  ·
                    refine ⟨1175521531951123336571617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269448170405991128381957 1175521531951123336571617)
                    ·
                      refine ⟨881641148963342502428713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175521531951123336571617 881641148963342502428713)
                      ·
                        rfl

theorem cell23_1716990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1716990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716990 prefixEnd_1716990 := by exact prefixLift 1716990
  have htrace : WordTrace (prefixWord ++ tailWord_1716990) baseStart_1716990 baseEnd_1716990 := by
    simpa [prefixWord, tailWord_1716990, baseEnd_1716990] using wordTrace_append hprefix tailTrace_1716990
  have hstable : (prefixWord ++ tailWord_1716990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716990).length < 2 ^ (prefixWord ++ tailWord_1716990).sum := by decide
  have hdescent : baseEnd_1716990 < baseStart_1716990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716994 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_1716994 : Nat := 118140960795 + 1716994 * 2 ^ 59
def prefixEnd_1716994 : Nat := 4983230072969 + 3 ^ 40 * 1716994 * 2
def baseEnd_1716994 : Nat := 881643202885960486778695

theorem tailTrace_1716994 : CollatzResearch.WordTrace tailWord_1716994 prefixEnd_1716994 881643202885960486778695 := by
  unfold tailWord_1716994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655978985407863018585509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41749277294420968049561357 15655978985407863018585509)
  ·
    refine ⟨2935496059763974315984783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15655978985407863018585509 2935496059763974315984783)
    ·
      refine ⟨4403244089645961473977175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2935496059763974315984783 4403244089645961473977175)
      ·
        refine ⟨6604866134468942210965763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403244089645961473977175 6604866134468942210965763)
        ·
          refine ⟨9907299201703413316448645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604866134468942210965763 9907299201703413316448645)
          ·
            refine ⟨1857618600319389996834121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9907299201703413316448645 1857618600319389996834121)
            ·
              refine ⟨1393213950239542497625591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857618600319389996834121 1393213950239542497625591)
              ·
                refine ⟨2089820925359313746438387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393213950239542497625591 2089820925359313746438387)
                ·
                  refine ⟨3134731388038970619657581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089820925359313746438387 3134731388038970619657581)
                  ·
                    refine ⟨1175524270514613982371593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134731388038970619657581 1175524270514613982371593)
                    ·
                      refine ⟨881643202885960486778695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175524270514613982371593 881643202885960486778695)
                      ·
                        rfl

theorem cell23_1716994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_1716994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1716994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1716994 prefixEnd_1716994 := by exact prefixLift 1716994
  have htrace : WordTrace (prefixWord ++ tailWord_1716994) baseStart_1716994 baseEnd_1716994 := by
    simpa [prefixWord, tailWord_1716994, baseEnd_1716994] using wordTrace_append hprefix tailTrace_1716994
  have hstable : (prefixWord ++ tailWord_1716994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716994).length < 2 ^ (prefixWord ++ tailWord_1716994).sum := by decide
  have hdescent : baseEnd_1716994 < baseStart_1716994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717026 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1717026 : Nat := 118140960795 + 1717026 * 2 ^ 59
def prefixEnd_1717026 : Nat := 4983230072969 + 3 ^ 40 * 1717026 * 2
def baseEnd_1717026 : Nat := 293886544755634787192849

theorem tailTrace_1717026 : CollatzResearch.WordTrace tailWord_1717026 prefixEnd_1717026 293886544755634787192849 := by
  unfold tailWord_1717026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656270769378880384876733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41750055385010347693004621 15656270769378880384876733)
  ·
    refine ⟨5871101538517080144328775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15656270769378880384876733 5871101538517080144328775)
    ·
      refine ⟨8806652307775620216493163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871101538517080144328775 8806652307775620216493163)
      ·
        refine ⟨13209978461663430324739745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8806652307775620216493163 13209978461663430324739745)
        ·
          refine ⟨9907483846247572743554809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13209978461663430324739745 9907483846247572743554809)
          ·
            refine ⟨7430612884685679557666107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9907483846247572743554809 7430612884685679557666107)
            ·
              refine ⟨11145919327028519336499161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430612884685679557666107 11145919327028519336499161)
              ·
                refine ⟨8359439495271389502374371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11145919327028519336499161 8359439495271389502374371)
                ·
                  refine ⟨12539159242907084253561557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359439495271389502374371 12539159242907084253561557)
                  ·
                    refine ⟨293886544755634787192849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12539159242907084253561557 293886544755634787192849)
                    ·
                      rfl

theorem cell23_1717026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1717026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717026 prefixEnd_1717026 := by exact prefixLift 1717026
  have htrace : WordTrace (prefixWord ++ tailWord_1717026) baseStart_1717026 baseEnd_1717026 := by
    simpa [prefixWord, tailWord_1717026, baseEnd_1717026] using wordTrace_append hprefix tailTrace_1717026
  have hstable : (prefixWord ++ tailWord_1717026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717026).length < 2 ^ (prefixWord ++ tailWord_1717026).sum := by decide
  have hdescent : baseEnd_1717026 < baseStart_1717026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717056 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_1717056 : Nat := 118140960795 + 1717056 * 2 ^ 59
def prefixEnd_1717056 : Nat := 4983230072969 + 3 ^ 40 * 1717056 * 2
def baseEnd_1717056 : Nat := 293891679562179748067803

theorem tailTrace_1717056 : CollatzResearch.WordTrace tailWord_1717056 prefixEnd_1717056 293891679562179748067803 := by
  unfold tailWord_1717056
  simp only [CollatzResearch.WordTrace]
  refine ⟨31313088633703418331549511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41750784844937891108732681 31313088633703418331549511)
  ·
    refine ⟨46969632950555127497324267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31313088633703418331549511 46969632950555127497324267)
    ·
      refine ⟨70454449425832691245986401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46969632950555127497324267 70454449425832691245986401)
      ·
        refine ⟨52840837069374518434489801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70454449425832691245986401 52840837069374518434489801)
        ·
          refine ⟨39630627802030888825867351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52840837069374518434489801 39630627802030888825867351)
          ·
            refine ⟨59445941703046333238801027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39630627802030888825867351 59445941703046333238801027)
            ·
              refine ⟨89168912554569499858201541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59445941703046333238801027 89168912554569499858201541)
              ·
                refine ⟨16719171103981781223412789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89168912554569499858201541 16719171103981781223412789)
                ·
                  refine ⟨1567422290998291989694949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16719171103981781223412789 1567422290998291989694949)
                  ·
                    refine ⟨293891679562179748067803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567422290998291989694949 293891679562179748067803)
                    ·
                      rfl

theorem cell23_1717056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_1717056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717056 prefixEnd_1717056 := by exact prefixLift 1717056
  have htrace : WordTrace (prefixWord ++ tailWord_1717056) baseStart_1717056 baseEnd_1717056 := by
    simpa [prefixWord, tailWord_1717056, baseEnd_1717056] using wordTrace_append hprefix tailTrace_1717056
  have hstable : (prefixWord ++ tailWord_1717056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717056).length < 2 ^ (prefixWord ++ tailWord_1717056).sum := by decide
  have hdescent : baseEnd_1717056 < baseStart_1717056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717066 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_1717066 : Nat := 118140960795 + 1717066 * 2 ^ 59
def prefixEnd_1717066 : Nat := 4983230072969 + 3 ^ 40 * 1717066 * 2
def baseEnd_1717066 : Nat := 881680173493084205078363

theorem tailTrace_1717066 : CollatzResearch.WordTrace tailWord_1717066 prefixEnd_1717066 881680173493084205078363 := by
  unfold tailWord_1717066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656635499342652092740763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41751027998247072247308701 15656635499342652092740763)
  ·
    refine ⟨23484953249013978139111145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656635499342652092740763 23484953249013978139111145)
    ·
      refine ⟨17613714936760483604333359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23484953249013978139111145 17613714936760483604333359)
      ·
        refine ⟨26420572405140725406500039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17613714936760483604333359 26420572405140725406500039)
        ·
          refine ⟨39630858607711088109750059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26420572405140725406500039 39630858607711088109750059)
          ·
            refine ⟨59446287911566632164625089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39630858607711088109750059 59446287911566632164625089)
            ·
              refine ⟨44584715933674974123468817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59446287911566632164625089 44584715933674974123468817)
              ·
                refine ⟨33438536950256230592601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44584715933674974123468817 33438536950256230592601613)
                ·
                  refine ⟨12539451356346086472225605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33438536950256230592601613 12539451356346086472225605)
                  ·
                    refine ⟨2351147129314891213542301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12539451356346086472225605 2351147129314891213542301)
                    ·
                      refine ⟨881680173493084205078363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2351147129314891213542301 881680173493084205078363)
                      ·
                        rfl

theorem cell23_1717066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_1717066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717066 prefixEnd_1717066 := by exact prefixLift 1717066
  have htrace : WordTrace (prefixWord ++ tailWord_1717066) baseStart_1717066 baseEnd_1717066 := by
    simpa [prefixWord, tailWord_1717066, baseEnd_1717066] using wordTrace_append hprefix tailTrace_1717066
  have hstable : (prefixWord ++ tailWord_1717066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717066).length < 2 ^ (prefixWord ++ tailWord_1717066).sum := by decide
  have hdescent : baseEnd_1717066 < baseStart_1717066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717140 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_1717140 : Nat := 118140960795 + 1717140 * 2 ^ 59
def prefixEnd_1717140 : Nat := 4983230072969 + 3 ^ 40 * 1717140 * 2
def baseEnd_1717140 : Nat := 881718171061516915553023

theorem tailTrace_1717140 : CollatzResearch.WordTrace tailWord_1717140 prefixEnd_1717140 881718171061516915553023 := by
  unfold tailWord_1717140
  simp only [CollatzResearch.WordTrace]
  refine ⟨31314620499551259504578437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41752827332735012672771249 31314620499551259504578437)
  ·
    refine ⟨5871491343665861157108457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31314620499551259504578437 5871491343665861157108457)
    ·
      refine ⟨4403618507749395867831343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5871491343665861157108457 4403618507749395867831343)
      ·
        refine ⟨6605427761624093801747015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403618507749395867831343 6605427761624093801747015)
        ·
          refine ⟨9908141642436140702620523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605427761624093801747015 9908141642436140702620523)
          ·
            refine ⟨14862212463654211053930785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9908141642436140702620523 14862212463654211053930785)
            ·
              refine ⟨11146659347740658290448089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14862212463654211053930785 11146659347740658290448089)
              ·
                refine ⟨8359994510805493717836067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11146659347740658290448089 8359994510805493717836067)
                ·
                  refine ⟨12539991766208240576754101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359994510805493717836067 12539991766208240576754101)
                  ·
                    refine ⟨1175624228082022554070697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12539991766208240576754101 1175624228082022554070697)
                    ·
                      refine ⟨881718171061516915553023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175624228082022554070697 881718171061516915553023)
                      ·
                        rfl

theorem cell23_1717140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_1717140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717140 prefixEnd_1717140 := by exact prefixLift 1717140
  have htrace : WordTrace (prefixWord ++ tailWord_1717140) baseStart_1717140 baseEnd_1717140 := by
    simpa [prefixWord, tailWord_1717140, baseEnd_1717140] using wordTrace_append hprefix tailTrace_1717140
  have hstable : (prefixWord ++ tailWord_1717140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717140).length < 2 ^ (prefixWord ++ tailWord_1717140).sum := by decide
  have hdescent : baseEnd_1717140 < baseStart_1717140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717173 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1717173 : Nat := 118140960795 + 1717173 * 2 ^ 59
def prefixEnd_1717173 : Nat := 4983230072969 + 3 ^ 40 * 1717173 * 2
def baseEnd_1717173 : Nat := 881735115923115286440371

theorem tailTrace_1717173 : CollatzResearch.WordTrace tailWord_1717173 prefixEnd_1717173 881735115923115286440371 := by
  unfold tailWord_1717173
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630444607982965645108173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41753629738655310430072115 62630444607982965645108173)
  ·
    refine ⟨23486416727993612116915565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62630444607982965645108173 23486416727993612116915565)
    ·
      refine ⟨8807406272997604543843337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23486416727993612116915565 8807406272997604543843337)
      ·
        refine ⟨6605554704748203407882503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8807406272997604543843337 6605554704748203407882503)
        ·
          refine ⟨9908332057122305111823755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605554704748203407882503 9908332057122305111823755)
          ·
            refine ⟨14862498085683457667735633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9908332057122305111823755 14862498085683457667735633)
            ·
              refine ⟨11146873564262593250801725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14862498085683457667735633 11146873564262593250801725)
              ·
                refine ⟨4180077586598472469050647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11146873564262593250801725 4180077586598472469050647)
                ·
                  refine ⟨6270116379897708703575971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180077586598472469050647 6270116379897708703575971)
                  ·
                    refine ⟨9405174569846563055363957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6270116379897708703575971 9405174569846563055363957)
                    ·
                      refine ⟨881735115923115286440371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9405174569846563055363957 881735115923115286440371)
                      ·
                        rfl

theorem cell23_1717173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1717173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717173 prefixEnd_1717173 := by exact prefixLift 1717173
  have htrace : WordTrace (prefixWord ++ tailWord_1717173) baseStart_1717173 baseEnd_1717173 := by
    simpa [prefixWord, tailWord_1717173, baseEnd_1717173] using wordTrace_append hprefix tailTrace_1717173
  have hstable : (prefixWord ++ tailWord_1717173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717173).length < 2 ^ (prefixWord ++ tailWord_1717173).sum := by decide
  have hdescent : baseEnd_1717173 < baseStart_1717173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717176 : List Nat := [2, 1, 2, 1, 2, 5, 10]
def baseStart_1717176 : Nat := 118140960795 + 1717176 * 2 ^ 59
def prefixEnd_1717176 : Nat := 4983230072969 + 3 ^ 40 * 1717176 * 2
def baseEnd_1717176 : Nat := 10885637732902207095097

theorem tailTrace_1717176 : CollatzResearch.WordTrace tailWord_1717176 prefixEnd_1717176 10885637732902207095097 := by
  unfold tailWord_1717176
  simp only [CollatzResearch.WordTrace]
  refine ⟨31315277013486048578733691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41753702684648064771644921 31315277013486048578733691)
  ·
    refine ⟨46972915520229072868100537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31315277013486048578733691 46972915520229072868100537)
    ·
      refine ⟨35229686640171804651075403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46972915520229072868100537 35229686640171804651075403)
      ·
        refine ⟨52844529960257706976613105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35229686640171804651075403 52844529960257706976613105)
        ·
          refine ⟨39633397470193280232459829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52844529960257706976613105 39633397470193280232459829)
          ·
            refine ⟨3715631012830620021793109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39633397470193280232459829 3715631012830620021793109)
            ·
              refine ⟨10885637732902207095097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3715631012830620021793109 10885637732902207095097)
              ·
                rfl

theorem cell23_1717176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 10].length) (baseStart_1717176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717176 prefixEnd_1717176 := by exact prefixLift 1717176
  have htrace : WordTrace (prefixWord ++ tailWord_1717176) baseStart_1717176 baseEnd_1717176 := by
    simpa [prefixWord, tailWord_1717176, baseEnd_1717176] using wordTrace_append hprefix tailTrace_1717176
  have hstable : (prefixWord ++ tailWord_1717176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717176).length < 2 ^ (prefixWord ++ tailWord_1717176).sum := by decide
  have hdescent : baseEnd_1717176 < baseStart_1717176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717210 : List Nat := [3, 1, 1, 2, 4, 3, 2, 7]
def baseStart_1717210 : Nat := 118140960795 + 1717210 * 2 ^ 59
def prefixEnd_1717210 : Nat := 4983230072969 + 3 ^ 40 * 1717210 * 2
def baseEnd_1717210 : Nat := 32657559803975245988063

theorem tailTrace_1717210 : CollatzResearch.WordTrace tailWord_1717210 prefixEnd_1717210 32657559803975245988063 := by
  unfold tailWord_1717210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657948527212230241051271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41754529405899280642803389 15657948527212230241051271)
  ·
    refine ⟨23486922790818345361576907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15657948527212230241051271 23486922790818345361576907)
    ·
      refine ⟨35230384186227518042365361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23486922790818345361576907 35230384186227518042365361)
      ·
        refine ⟨26422788139670638531774021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35230384186227518042365361 26422788139670638531774021)
        ·
          refine ⟨4954272776188244724707629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26422788139670638531774021 4954272776188244724707629)
          ·
            refine ⟨1857852291070591771765361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4954272776188244724707629 1857852291070591771765361)
            ·
              refine ⟨1393389218302943828824021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857852291070591771765361 1393389218302943828824021)
              ·
                refine ⟨32657559803975245988063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1393389218302943828824021 32657559803975245988063)
                ·
                  rfl

theorem cell23_1717210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_1717210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717210 prefixEnd_1717210 := by exact prefixLift 1717210
  have htrace : WordTrace (prefixWord ++ tailWord_1717210) baseStart_1717210 baseEnd_1717210 := by
    simpa [prefixWord, tailWord_1717210, baseEnd_1717210] using wordTrace_append hprefix tailTrace_1717210
  have hstable : (prefixWord ++ tailWord_1717210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717210).length < 2 ^ (prefixWord ++ tailWord_1717210).sum := by decide
  have hdescent : baseEnd_1717210 < baseStart_1717210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717238 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1717238 : Nat := 118140960795 + 1717238 * 2 ^ 59
def prefixEnd_1717238 : Nat := 4983230072969 + 3 ^ 40 * 1717238 * 2
def baseEnd_1717238 : Nat := 881768492165657532127573

theorem tailTrace_1717238 : CollatzResearch.WordTrace tailWord_1717238 prefixEnd_1717238 881768492165657532127573 := by
  unfold tailWord_1717238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914550959546717609139023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41755210235164987830816245 3914550959546717609139023)
  ·
    refine ⟨5871826439320076413708535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914550959546717609139023 5871826439320076413708535)
    ·
      refine ⟨8807739658980114620562803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871826439320076413708535 8807739658980114620562803)
      ·
        refine ⟨13211609488470171930844205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807739658980114620562803 13211609488470171930844205)
        ·
          refine ⟨4954353558176314474066577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13211609488470171930844205 4954353558176314474066577)
          ·
            refine ⟨3715765168632235855549933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4954353558176314474066577 3715765168632235855549933)
            ·
              refine ⟨1393411938237088445831225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3715765168632235855549933 1393411938237088445831225)
              ·
                refine ⟨1045058953677816334373419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393411938237088445831225 1045058953677816334373419)
                ·
                  refine ⟨1567588430516724501560129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045058953677816334373419 1567588430516724501560129)
                  ·
                    refine ⟨1175691322887543376170097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1567588430516724501560129 1175691322887543376170097)
                    ·
                      refine ⟨881768492165657532127573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175691322887543376170097 881768492165657532127573)
                      ·
                        rfl

theorem cell23_1717238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1717238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717238 prefixEnd_1717238 := by exact prefixLift 1717238
  have htrace : WordTrace (prefixWord ++ tailWord_1717238) baseStart_1717238 baseEnd_1717238 := by
    simpa [prefixWord, tailWord_1717238, baseEnd_1717238] using wordTrace_append hprefix tailTrace_1717238
  have hstable : (prefixWord ++ tailWord_1717238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717238).length < 2 ^ (prefixWord ++ tailWord_1717238).sum := by decide
  have hdescent : baseEnd_1717238 < baseStart_1717238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717320 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_1717320 : Nat := 118140960795 + 1717320 * 2 ^ 59
def prefixEnd_1717320 : Nat := 4983230072969 + 3 ^ 40 * 1717320 * 2
def baseEnd_1717320 : Nat := 881810597579326211302195

theorem tailTrace_1717320 : CollatzResearch.WordTrace tailWord_1717320 prefixEnd_1717320 881810597579326211302195 := by
  unfold tailWord_1717320
  simp only [CollatzResearch.WordTrace]
  refine ⟨31317903069225204875354707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41757204092300273167139609 31317903069225204875354707)
  ·
    refine ⟨46976854603837807313032061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31317903069225204875354707 46976854603837807313032061)
    ·
      refine ⟨17616320476439177742387023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46976854603837807313032061 17616320476439177742387023)
      ·
        refine ⟨26424480714658766613580535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17616320476439177742387023 26424480714658766613580535)
        ·
          refine ⟨39636721071988149920370803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26424480714658766613580535 39636721071988149920370803)
          ·
            refine ⟨59455081607982224880556205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39636721071988149920370803 59455081607982224880556205)
            ·
              refine ⟨22295655602993334330208577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59455081607982224880556205 22295655602993334330208577)
              ·
                refine ⟨16721741702245000747656433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22295655602993334330208577 16721741702245000747656433)
                ·
                  refine ⟨12541306276683750560742325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16721741702245000747656433 12541306276683750560742325)
                  ·
                    refine ⟨1175747463439101615069593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12541306276683750560742325 1175747463439101615069593)
                    ·
                      refine ⟨881810597579326211302195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175747463439101615069593 881810597579326211302195)
                      ·
                        rfl

theorem cell23_1717320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_1717320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717320 prefixEnd_1717320 := by exact prefixLift 1717320
  have htrace : WordTrace (prefixWord ++ tailWord_1717320) baseStart_1717320 baseEnd_1717320 := by
    simpa [prefixWord, tailWord_1717320, baseEnd_1717320] using wordTrace_append hprefix tailTrace_1717320
  have hstable : (prefixWord ++ tailWord_1717320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717320).length < 2 ^ (prefixWord ++ tailWord_1717320).sum := by decide
  have hdescent : baseEnd_1717320 < baseStart_1717320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717330 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1717330 : Nat := 118140960795 + 1717330 * 2 ^ 59
def prefixEnd_1717330 : Nat := 4983230072969 + 3 ^ 40 * 1717330 * 2
def baseEnd_1717330 : Nat := 293938577461957057392383

theorem tailTrace_1717330 : CollatzResearch.WordTrace tailWord_1717330 prefixEnd_1717330 293938577461957057392383 := by
  unfold tailWord_1717330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15659042717103545364643361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41757447245609454305715629 15659042717103545364643361)
  ·
    refine ⟨11744282037827659023482521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15659042717103545364643361 11744282037827659023482521)
    ·
      refine ⟨8808211528370744267611891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11744282037827659023482521 8808211528370744267611891)
      ·
        refine ⟨13212317292556116401417837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808211528370744267611891 13212317292556116401417837)
        ·
          refine ⟨4954618984708543650531689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13212317292556116401417837 4954618984708543650531689)
          ·
            refine ⟨3715964238531407737898767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4954618984708543650531689 3715964238531407737898767)
            ·
              refine ⟨5573946357797111606848151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715964238531407737898767 5573946357797111606848151)
              ·
                refine ⟨8360919536695667410272227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5573946357797111606848151 8360919536695667410272227)
                ·
                  refine ⟨12541379305043501115408341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8360919536695667410272227 12541379305043501115408341)
                  ·
                    refine ⟨293938577461957057392383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12541379305043501115408341 293938577461957057392383)
                    ·
                      rfl

theorem cell23_1717330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1717330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717330 prefixEnd_1717330 := by exact prefixLift 1717330
  have htrace : WordTrace (prefixWord ++ tailWord_1717330) baseStart_1717330 baseEnd_1717330 := by
    simpa [prefixWord, tailWord_1717330, baseEnd_1717330] using wordTrace_append hprefix tailTrace_1717330
  have hstable : (prefixWord ++ tailWord_1717330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717330).length < 2 ^ (prefixWord ++ tailWord_1717330).sum := by decide
  have hdescent : baseEnd_1717330 < baseStart_1717330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717377 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1717377 : Nat := 118140960795 + 1717377 * 2 ^ 59
def prefixEnd_1717377 : Nat := 4983230072969 + 3 ^ 40 * 1717377 * 2
def baseEnd_1717377 : Nat := 293946621992210829429811

theorem tailTrace_1717377 : CollatzResearch.WordTrace tailWord_1717377 prefixEnd_1717377 293946621992210829429811 := by
  unfold tailWord_1717377
  simp only [CollatzResearch.WordTrace]
  refine ⟨62637885099243908485534385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41758590066162605657022923 62637885099243908485534385)
  ·
    refine ⟨46978413824432931364150789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62637885099243908485534385 46978413824432931364150789)
    ·
      refine ⟨8808452592081174630778273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46978413824432931364150789 8808452592081174630778273)
      ·
        refine ⟨6606339444060880973083705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8808452592081174630778273 6606339444060880973083705)
        ·
          refine ⟨4954754583045660729812779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6606339444060880973083705 4954754583045660729812779)
          ·
            refine ⟨7432131874568491094719169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954754583045660729812779 7432131874568491094719169)
            ·
              refine ⟨5574098905926368321039377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432131874568491094719169 5574098905926368321039377)
              ·
                refine ⟨4180574179444776240779533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574098905926368321039377 4180574179444776240779533)
                ·
                  refine ⟨1567715317291791090292325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4180574179444776240779533 1567715317291791090292325)
                  ·
                    refine ⟨293946621992210829429811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567715317291791090292325 293946621992210829429811)
                    ·
                      rfl

theorem cell23_1717377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1717377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717377 prefixEnd_1717377 := by exact prefixLift 1717377
  have htrace : WordTrace (prefixWord ++ tailWord_1717377) baseStart_1717377 baseEnd_1717377 := by
    simpa [prefixWord, tailWord_1717377, baseEnd_1717377] using wordTrace_append hprefix tailTrace_1717377
  have hstable : (prefixWord ++ tailWord_1717377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717377).length < 2 ^ (prefixWord ++ tailWord_1717377).sum := by decide
  have hdescent : baseEnd_1717377 < baseStart_1717377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717390 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_1717390 : Nat := 118140960795 + 1717390 * 2 ^ 59
def prefixEnd_1717390 : Nat := 4983230072969 + 3 ^ 40 * 1717390 * 2
def baseEnd_1717390 : Nat := 97982949025015659714097

theorem tailTrace_1717390 : CollatzResearch.WordTrace tailWord_1717390 prefixEnd_1717390 97982949025015659714097 := by
  unfold tailWord_1717390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829794906024601463219703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41758906165464541137171749 7829794906024601463219703)
  ·
    refine ⟨11744692359036902194829555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7829794906024601463219703 11744692359036902194829555)
    ·
      refine ⟨17617038538555353292244333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11744692359036902194829555 17617038538555353292244333)
      ·
        refine ⟨6606389451958257484591625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17617038538555353292244333 6606389451958257484591625)
        ·
          refine ⟨4954792088968693113443719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6606389451958257484591625 4954792088968693113443719)
          ·
            refine ⟨7432188133453039670165579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954792088968693113443719 7432188133453039670165579)
            ·
              refine ⟨11148282200179559505248369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432188133453039670165579 11148282200179559505248369)
              ·
                refine ⟨8361211650134669628936277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11148282200179559505248369 8361211650134669628936277)
                ·
                  refine ⟨97982949025015659714097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8361211650134669628936277 97982949025015659714097)
                  ·
                    rfl

theorem cell23_1717390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_1717390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717390 prefixEnd_1717390 := by exact prefixLift 1717390
  have htrace : WordTrace (prefixWord ++ tailWord_1717390) baseStart_1717390 baseEnd_1717390 := by
    simpa [prefixWord, tailWord_1717390, baseEnd_1717390] using wordTrace_append hprefix tailTrace_1717390
  have hstable : (prefixWord ++ tailWord_1717390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717390).length < 2 ^ (prefixWord ++ tailWord_1717390).sum := by decide
  have hdescent : baseEnd_1717390 < baseStart_1717390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717437 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1717437 : Nat := 118140960795 + 1717437 * 2 ^ 59
def prefixEnd_1717437 : Nat := 4983230072969 + 3 ^ 40 * 1717437 * 2
def baseEnd_1717437 : Nat := 293956891605300751179719

theorem tailTrace_1717437 : CollatzResearch.WordTrace tailWord_1717437 prefixEnd_1717437 293956891605300751179719 := by
  unfold tailWord_1717437
  simp only [CollatzResearch.WordTrace]
  refine ⟨62640073479026538732718565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41760048986017692488479043 62640073479026538732718565)
  ·
    refine ⟨11745013777317476012384731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62640073479026538732718565 11745013777317476012384731)
    ·
      refine ⟨17617520665976214018577097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745013777317476012384731 17617520665976214018577097)
      ·
        refine ⟨13213140499482160513932823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17617520665976214018577097 13213140499482160513932823)
        ·
          refine ⟨19819710749223240770899235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213140499482160513932823 19819710749223240770899235)
          ·
            refine ⟨29729566123834861156348853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19819710749223240770899235 29729566123834861156348853)
            ·
              refine ⟨2787146824109518233407705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29729566123834861156348853 2787146824109518233407705)
              ·
                refine ⟨2090360118082138675055779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787146824109518233407705 2090360118082138675055779)
                ·
                  refine ⟨3135540177123208012583669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090360118082138675055779 3135540177123208012583669)
                  ·
                    refine ⟨293956891605300751179719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3135540177123208012583669 293956891605300751179719)
                    ·
                      rfl

theorem cell23_1717437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1717437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717437 prefixEnd_1717437 := by exact prefixLift 1717437
  have htrace : WordTrace (prefixWord ++ tailWord_1717437) baseStart_1717437 baseEnd_1717437 := by
    simpa [prefixWord, tailWord_1717437, baseEnd_1717437] using wordTrace_append hprefix tailTrace_1717437
  have hstable : (prefixWord ++ tailWord_1717437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717437).length < 2 ^ (prefixWord ++ tailWord_1717437).sum := by decide
  have hdescent : baseEnd_1717437 < baseStart_1717437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717450 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1717450 : Nat := 118140960795 + 1717450 * 2 ^ 59
def prefixEnd_1717450 : Nat := 4983230072969 + 3 ^ 40 * 1717450 * 2
def baseEnd_1717450 : Nat := 293959116688136900892199

theorem tailTrace_1717450 : CollatzResearch.WordTrace tailWord_1717450 prefixEnd_1717450 293959116688136900892199 := by
  unfold tailWord_1717450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660136906994860488235451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41760365085319627968627869 15660136906994860488235451)
  ·
    refine ⟨23490205360492290732353177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15660136906994860488235451 23490205360492290732353177)
    ·
      refine ⟨17617654020369218049264883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23490205360492290732353177 17617654020369218049264883)
      ·
        refine ⟨26426481030553827073897325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17617654020369218049264883 26426481030553827073897325)
        ·
          refine ⟨9909930386457685152711497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26426481030553827073897325 9909930386457685152711497)
          ·
            refine ⟨7432447789843263864533623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9909930386457685152711497 7432447789843263864533623)
            ·
              refine ⟨11148671684764895796800435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432447789843263864533623 11148671684764895796800435)
              ·
                refine ⟨16723007527147343695200653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11148671684764895796800435 16723007527147343695200653)
                ·
                  refine ⟨6271127822680253885700245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16723007527147343695200653 6271127822680253885700245)
                  ·
                    refine ⟨293959116688136900892199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6271127822680253885700245 293959116688136900892199)
                    ·
                      rfl

theorem cell23_1717450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1717450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717450 prefixEnd_1717450 := by exact prefixLift 1717450
  have htrace : WordTrace (prefixWord ++ tailWord_1717450) baseStart_1717450 baseEnd_1717450 := by
    simpa [prefixWord, tailWord_1717450, baseEnd_1717450] using wordTrace_append hprefix tailTrace_1717450
  have hstable : (prefixWord ++ tailWord_1717450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717450).length < 2 ^ (prefixWord ++ tailWord_1717450).sum := by decide
  have hdescent : baseEnd_1717450 < baseStart_1717450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717462 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1717462 : Nat := 118140960795 + 1717462 * 2 ^ 59
def prefixEnd_1717462 : Nat := 4983230072969 + 3 ^ 40 * 1717462 * 2
def baseEnd_1717462 : Nat := 293961170610754885242181

theorem tailTrace_1717462 : CollatzResearch.WordTrace tailWord_1717462 prefixEnd_1717462 293961170610754885242181 := by
  unfold tailWord_1717462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915061581495998000148665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41760656869290645334919093 3915061581495998000148665)
  ·
    refine ⟨2936296186121998500111499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915061581495998000148665 2936296186121998500111499)
    ·
      refine ⟨4404444279182997750167249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936296186121998500111499 4404444279182997750167249)
      ·
        refine ⟨3303333209387248312625437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4404444279182997750167249 3303333209387248312625437)
        ·
          refine ⟨1238749953520218117234539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3303333209387248312625437 1238749953520218117234539)
          ·
            refine ⟨1858124930280327175851809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238749953520218117234539 1858124930280327175851809)
            ·
              refine ⟨1393593697710245381888857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858124930280327175851809 1393593697710245381888857)
              ·
                refine ⟨1045195273282684036416643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393593697710245381888857 1045195273282684036416643)
                ·
                  refine ⟨1567792909924026054624965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045195273282684036416643 1567792909924026054624965)
                  ·
                    refine ⟨293961170610754885242181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567792909924026054624965 293961170610754885242181)
                    ·
                      rfl

theorem cell23_1717462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1717462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717462 prefixEnd_1717462 := by exact prefixLift 1717462
  have htrace : WordTrace (prefixWord ++ tailWord_1717462) baseStart_1717462 baseEnd_1717462 := by
    simpa [prefixWord, tailWord_1717462, baseEnd_1717462] using wordTrace_append hprefix tailTrace_1717462
  have hstable : (prefixWord ++ tailWord_1717462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717462).length < 2 ^ (prefixWord ++ tailWord_1717462).sum := by decide
  have hdescent : baseEnd_1717462 < baseStart_1717462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717494 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1717494 : Nat := 118140960795 + 1717494 * 2 ^ 59
def prefixEnd_1717494 : Nat := 4983230072969 + 3 ^ 40 * 1717494 * 2
def baseEnd_1717494 : Nat := 881899943213208530526395

theorem tailTrace_1717494 : CollatzResearch.WordTrace tailWord_1717494 prefixEnd_1717494 881899943213208530526395 := by
  unfold tailWord_1717494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915134527488752341721471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41761434959880024978362357 3915134527488752341721471)
  ·
    refine ⟨5872701791233128512582207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915134527488752341721471 5872701791233128512582207)
    ·
      refine ⟨8809052686849692768873311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5872701791233128512582207 8809052686849692768873311)
      ·
        refine ⟨13213579030274539153309967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809052686849692768873311 13213579030274539153309967)
        ·
          refine ⟨19820368545411808729964951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213579030274539153309967 19820368545411808729964951)
          ·
            refine ⟨29730552818117713094947427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19820368545411808729964951 29730552818117713094947427)
            ·
              refine ⟨44595829227176569642421141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29730552818117713094947427 44595829227176569642421141)
              ·
                refine ⟨2090429495023901701988491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44595829227176569642421141 2090429495023901701988491)
                ·
                  refine ⟨3135644242535852552982737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090429495023901701988491 3135644242535852552982737)
                  ·
                    refine ⟨2351733181901889414737053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3135644242535852552982737 2351733181901889414737053)
                    ·
                      refine ⟨881899943213208530526395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2351733181901889414737053 881899943213208530526395)
                      ·
                        rfl

theorem cell23_1717494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1717494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717494 prefixEnd_1717494 := by exact prefixLift 1717494
  have htrace : WordTrace (prefixWord ++ tailWord_1717494) baseStart_1717494 baseEnd_1717494 := by
    simpa [prefixWord, tailWord_1717494, baseEnd_1717494] using wordTrace_append hprefix tailTrace_1717494
  have hstable : (prefixWord ++ tailWord_1717494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717494).length < 2 ^ (prefixWord ++ tailWord_1717494).sum := by decide
  have hdescent : baseEnd_1717494 < baseStart_1717494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717507 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1717507 : Nat := 118140960795 + 1717507 * 2 ^ 59
def prefixEnd_1717507 : Nat := 4983230072969 + 3 ^ 40 * 1717507 * 2
def baseEnd_1717507 : Nat := 881906618461716979663835

theorem tailTrace_1717507 : CollatzResearch.WordTrace tailWord_1717507 prefixEnd_1717507 881906618461716979663835 := by
  unfold tailWord_1717507
  simp only [CollatzResearch.WordTrace]
  refine ⟨62642626588772940687766775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41761751059181960458511183 62642626588772940687766775)
  ·
    refine ⟨93963939883159411031650163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62642626588772940687766775 93963939883159411031650163)
    ·
      refine ⟨140945909824739116547475245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93963939883159411031650163 140945909824739116547475245)
      ·
        refine ⟨52854716184277168705303217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140945909824739116547475245 52854716184277168705303217)
        ·
          refine ⟨39641037138207876528977413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52854716184277168705303217 39641037138207876528977413)
          ·
            refine ⟨7432694463413976849183265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39641037138207876528977413 7432694463413976849183265)
            ·
              refine ⟨5574520847560482636887449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432694463413976849183265 5574520847560482636887449)
              ·
                refine ⟨4180890635670361977665587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574520847560482636887449 4180890635670361977665587)
                ·
                  refine ⟨6271335953505542966498381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180890635670361977665587 6271335953505542966498381)
                  ·
                    refine ⟨2351750982564578612436893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6271335953505542966498381 2351750982564578612436893)
                    ·
                      refine ⟨881906618461716979663835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2351750982564578612436893 881906618461716979663835)
                      ·
                        rfl

theorem cell23_1717507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1717507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717507 prefixEnd_1717507 := by exact prefixLift 1717507
  have htrace : WordTrace (prefixWord ++ tailWord_1717507) baseStart_1717507 baseEnd_1717507 := by
    simpa [prefixWord, tailWord_1717507, baseEnd_1717507] using wordTrace_append hprefix tailTrace_1717507
  have hstable : (prefixWord ++ tailWord_1717507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717507).length < 2 ^ (prefixWord ++ tailWord_1717507).sum := by decide
  have hdescent : baseEnd_1717507 < baseStart_1717507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717508 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1717508 : Nat := 118140960795 + 1717508 * 2 ^ 59
def prefixEnd_1717508 : Nat := 4983230072969 + 3 ^ 40 * 1717508 * 2
def baseEnd_1717508 : Nat := 881907131942371475751331

theorem tailTrace_1717508 : CollatzResearch.WordTrace tailWord_1717508 prefixEnd_1717508 881907131942371475751331 := by
  unfold tailWord_1717508
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321331530884658929276589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41761775374512878572368785 31321331530884658929276589)
  ·
    refine ⟨11745499324081747098478721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31321331530884658929276589 11745499324081747098478721)
    ·
      refine ⟨8809124493061310323859041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11745499324081747098478721 8809124493061310323859041)
      ·
        refine ⟨6606843369795982742894281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8809124493061310323859041 6606843369795982742894281)
        ·
          refine ⟨4955132527346987057170711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6606843369795982742894281 4955132527346987057170711)
          ·
            refine ⟨7432698791020480585756067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955132527346987057170711 7432698791020480585756067)
            ·
              refine ⟨11149048186530720878634101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432698791020480585756067 11149048186530720878634101)
              ·
                refine ⟨1045223267487255082371947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11149048186530720878634101 1045223267487255082371947)
                ·
                  refine ⟨1567834901230882623557921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045223267487255082371947 1567834901230882623557921)
                  ·
                    refine ⟨1175876175923161967668441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1567834901230882623557921 1175876175923161967668441)
                    ·
                      refine ⟨881907131942371475751331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175876175923161967668441 881907131942371475751331)
                      ·
                        rfl

theorem cell23_1717508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1717508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717508 prefixEnd_1717508 := by exact prefixLift 1717508
  have htrace : WordTrace (prefixWord ++ tailWord_1717508) baseStart_1717508 baseEnd_1717508 := by
    simpa [prefixWord, tailWord_1717508, baseEnd_1717508] using wordTrace_append hprefix tailTrace_1717508
  have hstable : (prefixWord ++ tailWord_1717508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717508).length < 2 ^ (prefixWord ++ tailWord_1717508).sum := by decide
  have hdescent : baseEnd_1717508 < baseStart_1717508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717547 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 7, 4, 2]
def baseStart_1717547 : Nat := 118140960795 + 1717547 * 2 ^ 59
def prefixEnd_1717547 : Nat := 4983230072969 + 3 ^ 40 * 1717547 * 2
def baseEnd_1717547 : Nat := 881927157687896823163651

theorem tailTrace_1717547 : CollatzResearch.WordTrace tailWord_1717547 prefixEnd_1717547 881927157687896823163651 := by
  unfold tailWord_1717547
  simp only [CollatzResearch.WordTrace]
  refine ⟨62644085508628027519222895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41762723672418685012815263 62644085508628027519222895)
  ·
    refine ⟨93966128262942041278834343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62644085508628027519222895 93966128262942041278834343)
    ·
      refine ⟨140949192394413061918251515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93966128262942041278834343 140949192394413061918251515)
      ·
        refine ⟨211423788591619592877377273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140949192394413061918251515 211423788591619592877377273)
        ·
          refine ⟨158567841443714694658032955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211423788591619592877377273 158567841443714694658032955)
          ·
            refine ⟨237851762165572041987049433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158567841443714694658032955 237851762165572041987049433)
            ·
              refine ⟨178388821624179031490287075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237851762165572041987049433 178388821624179031490287075)
              ·
                refine ⟨267583232436268547235430613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178388821624179031490287075 267583232436268547235430613)
                ·
                  refine ⟨6271482010225044075830405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 267583232436268547235430613 6271482010225044075830405)
                  ·
                    refine ⟨1175902876917195764218201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271482010225044075830405 1175902876917195764218201)
                    ·
                      refine ⟨881927157687896823163651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1175902876917195764218201 881927157687896823163651)
                      ·
                        rfl

theorem cell23_1717547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4, 2].length) (baseStart_1717547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717547 prefixEnd_1717547 := by exact prefixLift 1717547
  have htrace : WordTrace (prefixWord ++ tailWord_1717547) baseStart_1717547 baseEnd_1717547 := by
    simpa [prefixWord, tailWord_1717547, baseEnd_1717547] using wordTrace_append hprefix tailTrace_1717547
  have hstable : (prefixWord ++ tailWord_1717547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717547).length < 2 ^ (prefixWord ++ tailWord_1717547).sum := by decide
  have hdescent : baseEnd_1717547 < baseStart_1717547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717567 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1717567 : Nat := 118140960795 + 1717567 * 2 ^ 59
def prefixEnd_1717567 : Nat := 4983230072969 + 3 ^ 40 * 1717567 * 2
def baseEnd_1717567 : Nat := 881937427300986744913559

theorem tailTrace_1717567 : CollatzResearch.WordTrace tailWord_1717567 prefixEnd_1717567 881937427300986744913559 := by
  unfold tailWord_1717567
  simp only [CollatzResearch.WordTrace]
  refine ⟨62644814968555570934950955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41763209979037047289967303 62644814968555570934950955)
  ·
    refine ⟨93967222452833356402426433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62644814968555570934950955 93967222452833356402426433)
    ·
      refine ⟨70475416839625017301819825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93967222452833356402426433 70475416839625017301819825)
      ·
        refine ⟨52856562629718762976364869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70475416839625017301819825 52856562629718762976364869)
        ·
          refine ⟨9910605493072268058068413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52856562629718762976364869 9910605493072268058068413)
          ·
            refine ⟨3716477059902100521775655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9910605493072268058068413 3716477059902100521775655)
            ·
              refine ⟨5574715589853150782663483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716477059902100521775655 5574715589853150782663483)
              ·
                refine ⟨8362073384779726173995225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5574715589853150782663483 8362073384779726173995225)
                ·
                  refine ⟨6271555038584794630496419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8362073384779726173995225 6271555038584794630496419)
                  ·
                    refine ⟨9407332557877191945744629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6271555038584794630496419 9407332557877191945744629)
                    ·
                      refine ⟨881937427300986744913559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9407332557877191945744629 881937427300986744913559)
                      ·
                        rfl

theorem cell23_1717567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1717567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717567 prefixEnd_1717567 := by exact prefixLift 1717567
  have htrace : WordTrace (prefixWord ++ tailWord_1717567) baseStart_1717567 baseEnd_1717567 := by
    simpa [prefixWord, tailWord_1717567, baseEnd_1717567] using wordTrace_append hprefix tailTrace_1717567
  have hstable : (prefixWord ++ tailWord_1717567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717567).length < 2 ^ (prefixWord ++ tailWord_1717567).sum := by decide
  have hdescent : baseEnd_1717567 < baseStart_1717567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717617 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_1717617 : Nat := 118140960795 + 1717617 * 2 ^ 59
def prefixEnd_1717617 : Nat := 4983230072969 + 3 ^ 40 * 1717617 * 2
def baseEnd_1717617 : Nat := 293987700444570516429443

theorem tailTrace_1717617 : CollatzResearch.WordTrace tailWord_1717617 prefixEnd_1717617 293987700444570516429443 := by
  unfold tailWord_1717617
  simp only [CollatzResearch.WordTrace]
  refine ⟨62646638618374429474271105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41764425745582952982847403 62646638618374429474271105)
  ·
    refine ⟨46984978963780822105703329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62646638618374429474271105 46984978963780822105703329)
    ·
      refine ⟨35238734222835616579277497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46984978963780822105703329 35238734222835616579277497)
      ·
        refine ⟨26429050667126712434458123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35238734222835616579277497 26429050667126712434458123)
        ·
          refine ⟨39643576000690068651687185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26429050667126712434458123 39643576000690068651687185)
          ·
            refine ⟨29732682000517551488765389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39643576000690068651687185 29732682000517551488765389)
            ·
              refine ⟨11149755750194081808287021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29732682000517551488765389 11149755750194081808287021)
              ·
                refine ⟨4181158406322780678107633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11149755750194081808287021 4181158406322780678107633)
                ·
                  refine ⟨3135868804742085508580725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181158406322780678107633 3135868804742085508580725)
                  ·
                    refine ⟨293987700444570516429443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3135868804742085508580725 293987700444570516429443)
                    ·
                      rfl

theorem cell23_1717617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_1717617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717617 prefixEnd_1717617 := by exact prefixLift 1717617
  have htrace : WordTrace (prefixWord ++ tailWord_1717617) baseStart_1717617 baseEnd_1717617 := by
    simpa [prefixWord, tailWord_1717617, baseEnd_1717617] using wordTrace_append hprefix tailTrace_1717617
  have hstable : (prefixWord ++ tailWord_1717617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717617).length < 2 ^ (prefixWord ++ tailWord_1717617).sum := by decide
  have hdescent : baseEnd_1717617 < baseStart_1717617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717664 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_1717664 : Nat := 118140960795 + 1717664 * 2 ^ 59
def prefixEnd_1717664 : Nat := 4983230072969 + 3 ^ 40 * 1717664 * 2
def baseEnd_1717664 : Nat := 293995744974824288466871

theorem tailTrace_1717664 : CollatzResearch.WordTrace tailWord_1717664 prefixEnd_1717664 293995744974824288466871 := by
  unfold tailWord_1717664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31324176424602078250616023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41765568566136104334154697 31324176424602078250616023)
  ·
    refine ⟨46986264636903117375924035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31324176424602078250616023 46986264636903117375924035)
    ·
      refine ⟨70479396955354676063886053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46986264636903117375924035 70479396955354676063886053)
      ·
        refine ⟨13214886929129001761978635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70479396955354676063886053 13214886929129001761978635)
        ·
          refine ⟨19822330393693502642967953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13214886929129001761978635 19822330393693502642967953)
          ·
            refine ⟨14866747795270126982225965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19822330393693502642967953 14866747795270126982225965)
            ·
              refine ⟨5575030423226297618334737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14866747795270126982225965 5575030423226297618334737)
              ·
                refine ⟨4181272817419723213751053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575030423226297618334737 4181272817419723213751053)
                ·
                  refine ⟨1567977306532396205156645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4181272817419723213751053 1567977306532396205156645)
                  ·
                    refine ⟨293995744974824288466871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567977306532396205156645 293995744974824288466871)
                    ·
                      rfl

theorem cell23_1717664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_1717664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717664 prefixEnd_1717664 := by exact prefixLift 1717664
  have htrace : WordTrace (prefixWord ++ tailWord_1717664) baseStart_1717664 baseEnd_1717664 := by
    simpa [prefixWord, tailWord_1717664, baseEnd_1717664] using wordTrace_append hprefix tailTrace_1717664
  have hstable : (prefixWord ++ tailWord_1717664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717664).length < 2 ^ (prefixWord ++ tailWord_1717664).sum := by decide
  have hdescent : baseEnd_1717664 < baseStart_1717664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717707 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 5, 5]
def baseStart_1717707 : Nat := 118140960795 + 1717707 * 2 ^ 59
def prefixEnd_1717707 : Nat := 4983230072969 + 3 ^ 40 * 1717707 * 2
def baseEnd_1717707 : Nat := 294003104864205399054305

theorem tailTrace_1717707 : CollatzResearch.WordTrace tailWord_1717707 prefixEnd_1717707 294003104864205399054305 := by
  unfold tailWord_1717707
  simp only [CollatzResearch.WordTrace]
  refine ⟨62649921188048374845047375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41766614125365583230031583 62649921188048374845047375)
  ·
    refine ⟨93974881782072562267571063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62649921188048374845047375 93974881782072562267571063)
    ·
      refine ⟨140962322673108843401356595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93974881782072562267571063 140962322673108843401356595)
      ·
        refine ⟨211443484009663265102034893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140962322673108843401356595 211443484009663265102034893)
        ·
          refine ⟨79291306503623724413263085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211443484009663265102034893 79291306503623724413263085)
          ·
            refine ⟨29734239938858896654973657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79291306503623724413263085 29734239938858896654973657)
            ·
              refine ⟨22300679954144172491230243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29734239938858896654973657 22300679954144172491230243)
              ·
                refine ⟨33451019931216258736845365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22300679954144172491230243 33451019931216258736845365)
                ·
                  refine ⟨3136033118551524256579253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33451019931216258736845365 3136033118551524256579253)
                  ·
                    refine ⟨294003104864205399054305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3136033118551524256579253 294003104864205399054305)
                    ·
                      rfl

theorem cell23_1717707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 5].length) (baseStart_1717707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717707 prefixEnd_1717707 := by exact prefixLift 1717707
  have htrace : WordTrace (prefixWord ++ tailWord_1717707) baseStart_1717707 baseEnd_1717707 := by
    simpa [prefixWord, tailWord_1717707, baseEnd_1717707] using wordTrace_append hprefix tailTrace_1717707
  have hstable : (prefixWord ++ tailWord_1717707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717707).length < 2 ^ (prefixWord ++ tailWord_1717707).sum := by decide
  have hdescent : baseEnd_1717707 < baseStart_1717707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717721 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 3]
def baseStart_1717721 : Nat := 118140960795 + 1717721 * 2 ^ 59
def prefixEnd_1717721 : Nat := 4983230072969 + 3 ^ 40 * 1717721 * 2
def baseEnd_1717721 : Nat := 882016503321779142387851

theorem tailTrace_1717721 : CollatzResearch.WordTrace tailWord_1717721 prefixEnd_1717721 882016503321779142387851 := by
  unfold tailWord_1717721
  simp only [CollatzResearch.WordTrace]
  refine ⟨62650431809997655236057017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41766954539998436824038011 62650431809997655236057017)
  ·
    refine ⟨46987823857498241427042763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62650431809997655236057017 46987823857498241427042763)
    ·
      refine ⟨70481735786247362140564145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46987823857498241427042763 70481735786247362140564145)
      ·
        refine ⟨52861301839685521605423109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70481735786247362140564145 52861301839685521605423109)
        ·
          refine ⟨9911494094941035301016833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52861301839685521605423109 9911494094941035301016833)
          ·
            refine ⟨7433620571205776475762625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9911494094941035301016833 7433620571205776475762625)
            ·
              refine ⟨5575215428404332356821969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433620571205776475762625 5575215428404332356821969)
              ·
                refine ⟨4181411571303249267616477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575215428404332356821969 4181411571303249267616477)
                ·
                  refine ⟨1568029339238718475356179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4181411571303249267616477 1568029339238718475356179)
                  ·
                    refine ⟨2352044008858077713034269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1568029339238718475356179 2352044008858077713034269)
                    ·
                      refine ⟨882016503321779142387851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352044008858077713034269 882016503321779142387851)
                      ·
                        rfl

theorem cell23_1717721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_1717721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717721 prefixEnd_1717721 := by exact prefixLift 1717721
  have htrace : WordTrace (prefixWord ++ tailWord_1717721) baseStart_1717721 baseEnd_1717721 := by
    simpa [prefixWord, tailWord_1717721, baseEnd_1717721] using wordTrace_append hprefix tailTrace_1717721
  have hstable : (prefixWord ++ tailWord_1717721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717721).length < 2 ^ (prefixWord ++ tailWord_1717721).sum := by decide
  have hdescent : baseEnd_1717721 < baseStart_1717721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717731 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1717731 : Nat := 118140960795 + 1717731 * 2 ^ 59
def prefixEnd_1717731 : Nat := 4983230072969 + 3 ^ 40 * 1717731 * 2
def baseEnd_1717731 : Nat := 882021638128324103262805

theorem tailTrace_1717731 : CollatzResearch.WordTrace tailWord_1717731 prefixEnd_1717731 882021638128324103262805 := by
  unfold tailWord_1717731
  simp only [CollatzResearch.WordTrace]
  refine ⟨62650796539961426943921047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41767197693307617962614031 62650796539961426943921047)
  ·
    refine ⟨93976194809942140415881571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62650796539961426943921047 93976194809942140415881571)
    ·
      refine ⟨140964292214913210623822357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93976194809942140415881571 140964292214913210623822357)
      ·
        refine ⟨6607701197574056747991673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140964292214913210623822357 6607701197574056747991673)
        ·
          refine ⟨4955775898180542560993755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6607701197574056747991673 4955775898180542560993755)
          ·
            refine ⟨7433663847270813841490633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955775898180542560993755 7433663847270813841490633)
            ·
              refine ⟨5575247885453110381117975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7433663847270813841490633 5575247885453110381117975)
              ·
                refine ⟨8362871828179665571676963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575247885453110381117975 8362871828179665571676963)
                ·
                  refine ⟨12544307742269498357515445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8362871828179665571676963 12544307742269498357515445)
                  ·
                    refine ⟨1176028850837765471017073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12544307742269498357515445 1176028850837765471017073)
                    ·
                      refine ⟨882021638128324103262805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176028850837765471017073 882021638128324103262805)
                      ·
                        rfl

theorem cell23_1717731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1717731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717731 prefixEnd_1717731 := by exact prefixLift 1717731
  have htrace : WordTrace (prefixWord ++ tailWord_1717731) baseStart_1717731 baseEnd_1717731 := by
    simpa [prefixWord, tailWord_1717731, baseEnd_1717731] using wordTrace_append hprefix tailTrace_1717731
  have hstable : (prefixWord ++ tailWord_1717731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717731).length < 2 ^ (prefixWord ++ tailWord_1717731).sum := by decide
  have hdescent : baseEnd_1717731 < baseStart_1717731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717754 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_1717754 : Nat := 118140960795 + 1717754 * 2 ^ 59
def prefixEnd_1717754 : Nat := 4983230072969 + 3 ^ 40 * 1717754 * 2
def baseEnd_1717754 : Nat := 294011149394459171091733

theorem tailTrace_1717754 : CollatzResearch.WordTrace tailWord_1717754 prefixEnd_1717754 294011149394459171091733 := by
  unfold tailWord_1717754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15662908854719525468002079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41767756945918734581338877 15662908854719525468002079)
  ·
    refine ⟨23494363282079288202003119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15662908854719525468002079 23494363282079288202003119)
    ·
      refine ⟨35241544923118932303004679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23494363282079288202003119 35241544923118932303004679)
      ·
        refine ⟨52862317384678398454507019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35241544923118932303004679 52862317384678398454507019)
        ·
          refine ⟨79293476077017597681760529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52862317384678398454507019 79293476077017597681760529)
          ·
            refine ⟨59470107057763198261320397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79293476077017597681760529 59470107057763198261320397)
            ·
              refine ⟨22301290146661199347995149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59470107057763198261320397 22301290146661199347995149)
              ·
                refine ⟨8362983804997949755498181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22301290146661199347995149 8362983804997949755498181)
                ·
                  refine ⟨1568059463437115579155909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8362983804997949755498181 1568059463437115579155909)
                  ·
                    refine ⟨294011149394459171091733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1568059463437115579155909 294011149394459171091733)
                    ·
                      rfl

theorem cell23_1717754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_1717754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717754 prefixEnd_1717754 := by exact prefixLift 1717754
  have htrace : WordTrace (prefixWord ++ tailWord_1717754) baseStart_1717754 baseEnd_1717754 := by
    simpa [prefixWord, tailWord_1717754, baseEnd_1717754] using wordTrace_append hprefix tailTrace_1717754
  have hstable : (prefixWord ++ tailWord_1717754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717754).length < 2 ^ (prefixWord ++ tailWord_1717754).sum := by decide
  have hdescent : baseEnd_1717754 < baseStart_1717754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717781 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_1717781 : Nat := 118140960795 + 1717781 * 2 ^ 59
def prefixEnd_1717781 : Nat := 4983230072969 + 3 ^ 40 * 1717781 * 2
def baseEnd_1717781 : Nat := 882047312161048907637575

theorem tailTrace_1717781 : CollatzResearch.WordTrace tailWord_1717781 prefixEnd_1717781 882047312161048907637575 := by
  unfold tailWord_1717781
  simp only [CollatzResearch.WordTrace]
  refine ⟨62652620189780285483241197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41768413459853523655494131 62652620189780285483241197)
  ·
    refine ⟨23494732571167607056215449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62652620189780285483241197 23494732571167607056215449)
    ·
      refine ⟨17621049428375705292161587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23494732571167607056215449 17621049428375705292161587)
      ·
        refine ⟨26431574142563557938242381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17621049428375705292161587 26431574142563557938242381)
        ·
          refine ⟨9911840303461334226840893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26431574142563557938242381 9911840303461334226840893)
          ·
            refine ⟨3716940113798000335065335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9911840303461334226840893 3716940113798000335065335)
            ·
              refine ⟨5575410170697000502598003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716940113798000335065335 5575410170697000502598003)
              ·
                refine ⟨8363115256045500753897005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575410170697000502598003 8363115256045500753897005)
                ·
                  refine ⟨3136168221017062782711377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8363115256045500753897005 3136168221017062782711377)
                  ·
                    refine ⟨2352126165762797087033533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3136168221017062782711377 2352126165762797087033533)
                    ·
                      refine ⟨882047312161048907637575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352126165762797087033533 882047312161048907637575)
                      ·
                        rfl

theorem cell23_1717781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_1717781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717781 prefixEnd_1717781 := by exact prefixLift 1717781
  have htrace : WordTrace (prefixWord ++ tailWord_1717781) baseStart_1717781 baseEnd_1717781 := by
    simpa [prefixWord, tailWord_1717781, baseEnd_1717781] using wordTrace_append hprefix tailTrace_1717781
  have hstable : (prefixWord ++ tailWord_1717781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717781).length < 2 ^ (prefixWord ++ tailWord_1717781).sum := by decide
  have hdescent : baseEnd_1717781 < baseStart_1717781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717807 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_1717807 : Nat := 118140960795 + 1717807 * 2 ^ 59
def prefixEnd_1717807 : Nat := 4983230072969 + 3 ^ 40 * 1717807 * 2
def baseEnd_1717807 : Nat := 882060662658065805912455

theorem tailTrace_1717807 : CollatzResearch.WordTrace tailWord_1717807 prefixEnd_1717807 882060662658065805912455 := by
  unfold tailWord_1717807
  simp only [CollatzResearch.WordTrace]
  refine ⟨62653568487686091923687675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41769045658457394615791783 62653568487686091923687675)
  ·
    refine ⟨93980352731529137885531513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62653568487686091923687675 93980352731529137885531513)
    ·
      refine ⟨70485264548646853414148635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93980352731529137885531513 70485264548646853414148635)
      ·
        refine ⟨105727896822970280121222953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70485264548646853414148635 105727896822970280121222953)
        ·
          refine ⟨79295922617227710090917215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105727896822970280121222953 79295922617227710090917215)
          ·
            refine ⟨118943883925841565136375823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79295922617227710090917215 118943883925841565136375823)
            ·
              refine ⟨178415825888762347704563735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118943883925841565136375823 178415825888762347704563735)
              ·
                refine ⟨267623738833143521556845603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178415825888762347704563735 267623738833143521556845603)
                ·
                  refine ⟨401435608249715282335268405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267623738833143521556845603 401435608249715282335268405)
                  ·
                    refine ⟨37634588273410807718931413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 401435608249715282335268405 37634588273410807718931413)
                    ·
                      refine ⟨882060662658065805912455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37634588273410807718931413 882060662658065805912455)
                      ·
                        rfl

theorem cell23_1717807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_1717807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717807 prefixEnd_1717807 := by exact prefixLift 1717807
  have htrace : WordTrace (prefixWord ++ tailWord_1717807) baseStart_1717807 baseEnd_1717807 := by
    simpa [prefixWord, tailWord_1717807, baseEnd_1717807] using wordTrace_append hprefix tailTrace_1717807
  have hstable : (prefixWord ++ tailWord_1717807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717807).length < 2 ^ (prefixWord ++ tailWord_1717807).sum := by decide
  have hdescent : baseEnd_1717807 < baseStart_1717807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717834 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1717834 : Nat := 118140960795 + 1717834 * 2 ^ 59
def prefixEnd_1717834 : Nat := 4983230072969 + 3 ^ 40 * 1717834 * 2
def baseEnd_1717834 : Nat := 882074526635737200274831

theorem tailTrace_1717834 : CollatzResearch.WordTrace tailWord_1717834 prefixEnd_1717834 882074526635737200274831 := by
  unfold tailWord_1717834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663638314647068883730139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41769702172392183689947037 15663638314647068883730139)
  ·
    refine ⟨23495457471970603325595209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15663638314647068883730139 23495457471970603325595209)
    ·
      refine ⟨17621593103977952494196407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23495457471970603325595209 17621593103977952494196407)
      ·
        refine ⟨26432389655966928741294611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17621593103977952494196407 26432389655966928741294611)
        ·
          refine ⟨39648584483950393111941917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26432389655966928741294611 39648584483950393111941917)
          ·
            refine ⟨14868219181481397416978219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39648584483950393111941917 14868219181481397416978219)
            ·
              refine ⟨22302328772222096125467329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14868219181481397416978219 22302328772222096125467329)
              ·
                refine ⟨16726746579166572094100497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22302328772222096125467329 16726746579166572094100497)
                ·
                  refine ⟨12545059934374929070575373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16726746579166572094100497 12545059934374929070575373)
                  ·
                    refine ⟨4704397475390598401465765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12545059934374929070575373 4704397475390598401465765)
                    ·
                      refine ⟨882074526635737200274831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4704397475390598401465765 882074526635737200274831)
                      ·
                        rfl

theorem cell23_1717834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1717834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717834 prefixEnd_1717834 := by exact prefixLift 1717834
  have htrace : WordTrace (prefixWord ++ tailWord_1717834) baseStart_1717834 baseEnd_1717834 := by
    simpa [prefixWord, tailWord_1717834, baseEnd_1717834] using wordTrace_append hprefix tailTrace_1717834
  have hstable : (prefixWord ++ tailWord_1717834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717834).length < 2 ^ (prefixWord ++ tailWord_1717834).sum := by decide
  have hdescent : baseEnd_1717834 < baseStart_1717834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717838 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_1717838 : Nat := 118140960795 + 1717838 * 2 ^ 59
def prefixEnd_1717838 : Nat := 4983230072969 + 3 ^ 40 * 1717838 * 2
def baseEnd_1717838 : Nat := 882076580558355184624813

theorem tailTrace_1717838 : CollatzResearch.WordTrace tailWord_1717838 prefixEnd_1717838 882076580558355184624813 := by
  unfold tailWord_1717838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831837393821723027258271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41769799433715856145377445 7831837393821723027258271)
  ·
    refine ⟨11747756090732584540887407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7831837393821723027258271 11747756090732584540887407)
    ·
      refine ⟨17621634136098876811331111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11747756090732584540887407 17621634136098876811331111)
      ·
        refine ⟨26432451204148315216996667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17621634136098876811331111 26432451204148315216996667)
        ·
          refine ⟨39648676806222472825495001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26432451204148315216996667 39648676806222472825495001)
          ·
            refine ⟨29736507604666854619121251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39648676806222472825495001 29736507604666854619121251)
            ·
              refine ⟨44604761407000281928681877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29736507604666854619121251 44604761407000281928681877)
              ·
                refine ⟨2090848190953138215406963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44604761407000281928681877 2090848190953138215406963)
                ·
                  refine ⟨3136272286429707323110445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090848190953138215406963 3136272286429707323110445)
                  ·
                    refine ⟨1176102107411140246166417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136272286429707323110445 1176102107411140246166417)
                    ·
                      refine ⟨882076580558355184624813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176102107411140246166417 882076580558355184624813)
                      ·
                        rfl

theorem cell23_1717838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_1717838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717838 prefixEnd_1717838 := by exact prefixLift 1717838
  have htrace : WordTrace (prefixWord ++ tailWord_1717838) baseStart_1717838 baseEnd_1717838 := by
    simpa [prefixWord, tailWord_1717838, baseEnd_1717838] using wordTrace_append hprefix tailTrace_1717838
  have hstable : (prefixWord ++ tailWord_1717838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717838).length < 2 ^ (prefixWord ++ tailWord_1717838).sum := by decide
  have hdescent : baseEnd_1717838 < baseStart_1717838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717844 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1717844 : Nat := 118140960795 + 1717844 * 2 ^ 59
def prefixEnd_1717844 : Nat := 4983230072969 + 3 ^ 40 * 1717844 * 2
def baseEnd_1717844 : Nat := 294026553814094053716595

theorem tailTrace_1717844 : CollatzResearch.WordTrace tailWord_1717844 prefixEnd_1717844 294026553814094053716595 := by
  unfold tailWord_1717844
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327458994276023621392293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41769945325701364828523057 31327458994276023621392293)
  ·
    refine ⟨5873898561426754429011055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31327458994276023621392293 5873898561426754429011055)
    ·
      refine ⟨8810847842140131643516583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873898561426754429011055 8810847842140131643516583)
      ·
        refine ⟨13216271763210197465274875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810847842140131643516583 13216271763210197465274875)
        ·
          refine ⟨19824407644815296197912313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13216271763210197465274875 19824407644815296197912313)
          ·
            refine ⟨14868305733611472148434235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19824407644815296197912313 14868305733611472148434235)
            ·
              refine ⟨22302458600417208222651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14868305733611472148434235 22302458600417208222651353)
              ·
                refine ⟨16726843950312906166988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22302458600417208222651353 16726843950312906166988515)
                ·
                  refine ⟨25090265925469359250482773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16726843950312906166988515 25090265925469359250482773)
                  ·
                    refine ⟨294026553814094053716595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25090265925469359250482773 294026553814094053716595)
                    ·
                      rfl

theorem cell23_1717844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1717844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717844 prefixEnd_1717844 := by exact prefixLift 1717844
  have htrace : WordTrace (prefixWord ++ tailWord_1717844) baseStart_1717844 baseEnd_1717844 := by
    simpa [prefixWord, tailWord_1717844, baseEnd_1717844] using wordTrace_append hprefix tailTrace_1717844
  have hstable : (prefixWord ++ tailWord_1717844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717844).length < 2 ^ (prefixWord ++ tailWord_1717844).sum := by decide
  have hdescent : baseEnd_1717844 < baseStart_1717844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717846 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1717846 : Nat := 118140960795 + 1717846 * 2 ^ 59
def prefixEnd_1717846 : Nat := 4983230072969 + 3 ^ 40 * 1717846 * 2
def baseEnd_1717846 : Nat := 882080688403591153324777

theorem tailTrace_1717846 : CollatzResearch.WordTrace tailWord_1717846 prefixEnd_1717846 882080688403591153324777 := by
  unfold tailWord_1717846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915936933409050099022337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41769993956363201056238261 3915936933409050099022337)
  ·
    refine ⟨2936952700056787574266753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915936933409050099022337 2936952700056787574266753)
    ·
      refine ⟨2202714525042590680700065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2936952700056787574266753 2202714525042590680700065)
      ·
        refine ⟨1652035893781943010525049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2202714525042590680700065 1652035893781943010525049)
        ·
          refine ⟨1239026920336457257893787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652035893781943010525049 1239026920336457257893787)
          ·
            refine ⟨1858540380504685886840681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239026920336457257893787 1858540380504685886840681)
            ·
              refine ⟨1393905285378514415130511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858540380504685886840681 1393905285378514415130511)
              ·
                refine ⟨2090857928067771622695767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393905285378514415130511 2090857928067771622695767)
                ·
                  refine ⟨3136286892101657434043651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090857928067771622695767 3136286892101657434043651)
                  ·
                    refine ⟨4704430338152486151065477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3136286892101657434043651 4704430338152486151065477)
                    ·
                      refine ⟨882080688403591153324777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4704430338152486151065477 882080688403591153324777)
                      ·
                        rfl

theorem cell23_1717846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1717846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717846 prefixEnd_1717846 := by exact prefixLift 1717846
  have htrace : WordTrace (prefixWord ++ tailWord_1717846) baseStart_1717846 baseEnd_1717846 := by
    simpa [prefixWord, tailWord_1717846, baseEnd_1717846] using wordTrace_append hprefix tailTrace_1717846
  have hstable : (prefixWord ++ tailWord_1717846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717846).length < 2 ^ (prefixWord ++ tailWord_1717846).sum := by decide
  have hdescent : baseEnd_1717846 < baseStart_1717846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717885 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_1717885 : Nat := 118140960795 + 1717885 * 2 ^ 59
def prefixEnd_1717885 : Nat := 4983230072969 + 3 ^ 40 * 1717885 * 2
def baseEnd_1717885 : Nat := 882100714149116500737097

theorem tailTrace_1717885 : CollatzResearch.WordTrace tailWord_1717885 prefixEnd_1717885 882100714149116500737097 := by
  unfold tailWord_1717885
  simp only [CollatzResearch.WordTrace]
  refine ⟨62656413381403511245027109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41770942254269007496684739 62656413381403511245027109)
  ·
    refine ⟨11748077509013158358442583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62656413381403511245027109 11748077509013158358442583)
    ·
      refine ⟨17622116263519737537663875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11748077509013158358442583 17622116263519737537663875)
      ·
        refine ⟨26433174395279606306495813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17622116263519737537663875 26433174395279606306495813)
        ·
          refine ⟨4956220199114926182467965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26433174395279606306495813 4956220199114926182467965)
          ·
            refine ⟨1858582574668097318425487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4956220199114926182467965 1858582574668097318425487)
            ·
              refine ⟨2787873862002145977638231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858582574668097318425487 2787873862002145977638231)
              ·
                refine ⟨4181810793003218966457347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787873862002145977638231 4181810793003218966457347)
                ·
                  refine ⟨6272716189504828449686021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181810793003218966457347 6272716189504828449686021)
                  ·
                    refine ⟨1176134285532155334316129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272716189504828449686021 1176134285532155334316129)
                    ·
                      refine ⟨882100714149116500737097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176134285532155334316129 882100714149116500737097)
                      ·
                        rfl

theorem cell23_1717885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_1717885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717885 prefixEnd_1717885 := by exact prefixLift 1717885
  have htrace : WordTrace (prefixWord ++ tailWord_1717885) baseStart_1717885 baseEnd_1717885 := by
    simpa [prefixWord, tailWord_1717885, baseEnd_1717885] using wordTrace_append hprefix tailTrace_1717885
  have hstable : (prefixWord ++ tailWord_1717885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717885).length < 2 ^ (prefixWord ++ tailWord_1717885).sum := by decide
  have hdescent : baseEnd_1717885 < baseStart_1717885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717904 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_1717904 : Nat := 118140960795 + 1717904 * 2 ^ 59
def prefixEnd_1717904 : Nat := 4983230072969 + 3 ^ 40 * 1717904 * 2
def baseEnd_1717904 : Nat := 294036823427183975466503

theorem tailTrace_1717904 : CollatzResearch.WordTrace tailWord_1717904 prefixEnd_1717904 294036823427183975466503 := by
  unfold tailWord_1717904
  simp only [CollatzResearch.WordTrace]
  refine ⟨31328553184167338744984383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41771404245556451659979177 31328553184167338744984383)
  ·
    refine ⟨46992829776251008117476575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31328553184167338744984383 46992829776251008117476575)
    ·
      refine ⟨70489244664376512176214863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46992829776251008117476575 70489244664376512176214863)
      ·
        refine ⟨105733866996564768264322295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70489244664376512176214863 105733866996564768264322295)
        ·
          refine ⟨158600800494847152396483443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105733866996564768264322295 158600800494847152396483443)
          ·
            refine ⟨237901200742270728594725165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158600800494847152396483443 237901200742270728594725165)
            ·
              refine ⟨89212950278351523223021937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237901200742270728594725165 89212950278351523223021937)
              ·
                refine ⟨66909712708763642417266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89212950278351523223021937 66909712708763642417266453)
                ·
                  refine ⟨3136392783223295738309365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66909712708763642417266453 3136392783223295738309365)
                  ·
                    refine ⟨294036823427183975466503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3136392783223295738309365 294036823427183975466503)
                    ·
                      rfl

theorem cell23_1717904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_1717904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717904 prefixEnd_1717904 := by exact prefixLift 1717904
  have htrace : WordTrace (prefixWord ++ tailWord_1717904) baseStart_1717904 baseEnd_1717904 := by
    simpa [prefixWord, tailWord_1717904, baseEnd_1717904] using wordTrace_append hprefix tailTrace_1717904
  have hstable : (prefixWord ++ tailWord_1717904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717904).length < 2 ^ (prefixWord ++ tailWord_1717904).sum := by decide
  have hdescent : baseEnd_1717904 < baseStart_1717904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717921 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1717921 : Nat := 118140960795 + 1717921 * 2 ^ 59
def prefixEnd_1717921 : Nat := 4983230072969 + 3 ^ 40 * 1717921 * 2
def baseEnd_1717921 : Nat := 294039733150892786628977

theorem tailTrace_1717921 : CollatzResearch.WordTrace tailWord_1717921 prefixEnd_1717921 294039733150892786628977 := by
  unfold tailWord_1717921
  simp only [CollatzResearch.WordTrace]
  refine ⟨62657726409273089393337617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41771817606182059595558411 62657726409273089393337617)
  ·
    refine ⟨46993294806954817045003213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62657726409273089393337617 46993294806954817045003213)
    ·
      refine ⟨17622485552608056391876205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46993294806954817045003213 17622485552608056391876205)
      ·
        refine ⟨6608432082228021146953577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17622485552608056391876205 6608432082228021146953577)
        ·
          refine ⟨4956324061671015860215183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6608432082228021146953577 4956324061671015860215183)
          ·
            refine ⟨7434486092506523790322775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956324061671015860215183 7434486092506523790322775)
            ·
              refine ⟨11151729138759785685484163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434486092506523790322775 11151729138759785685484163)
              ·
                refine ⟨16727593708139678528226245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11151729138759785685484163 16727593708139678528226245)
                ·
                  refine ⟨3136423820276189724042421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16727593708139678528226245 3136423820276189724042421)
                  ·
                    refine ⟨294039733150892786628977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3136423820276189724042421 294039733150892786628977)
                    ·
                      rfl

theorem cell23_1717921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1717921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717921 prefixEnd_1717921 := by exact prefixLift 1717921
  have htrace : WordTrace (prefixWord ++ tailWord_1717921) baseStart_1717921 baseEnd_1717921 := by
    simpa [prefixWord, tailWord_1717921, baseEnd_1717921] using wordTrace_append hprefix tailTrace_1717921
  have hstable : (prefixWord ++ tailWord_1717921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717921).length < 2 ^ (prefixWord ++ tailWord_1717921).sum := by decide
  have hdescent : baseEnd_1717921 < baseStart_1717921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717944 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1717944 : Nat := 118140960795 + 1717944 * 2 ^ 59
def prefixEnd_1717944 : Nat := 4983230072969 + 3 ^ 40 * 1717944 * 2
def baseEnd_1717944 : Nat := 882131009507731769899325

theorem tailTrace_1717944 : CollatzResearch.WordTrace tailWord_1717944 prefixEnd_1717944 882131009507731769899325 := by
  unfold tailWord_1717944
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329282644094882160712443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41772376858793176214283257 31329282644094882160712443)
  ·
    refine ⟨46993923966142323241068665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31329282644094882160712443 46993923966142323241068665)
    ·
      refine ⟨35245442974606742430801499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46993923966142323241068665 35245442974606742430801499)
      ·
        refine ⟨52868164461910113646202249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35245442974606742430801499 52868164461910113646202249)
        ·
          refine ⟨39651123346432585234651687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52868164461910113646202249 39651123346432585234651687)
          ·
            refine ⟨59476685019648877851977531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39651123346432585234651687 59476685019648877851977531)
            ·
              refine ⟨89215027529473316777966297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59476685019648877851977531 89215027529473316777966297)
              ·
                refine ⟨66911270647104987583474723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89215027529473316777966297 66911270647104987583474723)
                ·
                  refine ⟨100366905970657481375212085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66911270647104987583474723 100366905970657481375212085)
                  ·
                    refine ⟨9409397434749138878926133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100366905970657481375212085 9409397434749138878926133)
                    ·
                      refine ⟨882131009507731769899325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9409397434749138878926133 882131009507731769899325)
                      ·
                        rfl

theorem cell23_1717944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1717944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717944 prefixEnd_1717944 := by exact prefixLift 1717944
  have htrace : WordTrace (prefixWord ++ tailWord_1717944) baseStart_1717944 baseEnd_1717944 := by
    simpa [prefixWord, tailWord_1717944, baseEnd_1717944] using wordTrace_append hprefix tailTrace_1717944
  have hstable : (prefixWord ++ tailWord_1717944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717944).length < 2 ^ (prefixWord ++ tailWord_1717944).sum := by decide
  have hdescent : baseEnd_1717944 < baseStart_1717944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717951 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 5, 4]
def baseStart_1717951 : Nat := 118140960795 + 1717951 * 2 ^ 59
def prefixEnd_1717951 : Nat := 4983230072969 + 3 ^ 40 * 1717951 * 2
def baseEnd_1717951 : Nat := 294044867957437747503931

theorem tailTrace_1717951 : CollatzResearch.WordTrace tailWord_1717951 prefixEnd_1717951 294044867957437747503931 := by
  unfold tailWord_1717951
  simp only [CollatzResearch.WordTrace]
  refine ⟨62658820599164404516929707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41772547066109603011286471 62658820599164404516929707)
  ·
    refine ⟨93988230898746606775394561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62658820599164404516929707 93988230898746606775394561)
    ·
      refine ⟨70491173174059955081545921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93988230898746606775394561 70491173174059955081545921)
      ·
        refine ⟨52868379880544966311159441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70491173174059955081545921 52868379880544966311159441)
        ·
          refine ⟨39651284910408724733369581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52868379880544966311159441 39651284910408724733369581)
          ·
            refine ⟨14869231841403271775013593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39651284910408724733369581 14869231841403271775013593)
            ·
              refine ⟨11151923881052453831260195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14869231841403271775013593 11151923881052453831260195)
              ·
                refine ⟨16727885821578680746890293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11151923881052453831260195 16727885821578680746890293)
                ·
                  refine ⟨1568239295773001320020965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16727885821578680746890293 1568239295773001320020965)
                  ·
                    refine ⟨294044867957437747503931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1568239295773001320020965 294044867957437747503931)
                    ·
                      rfl

theorem cell23_1717951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_1717951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717951 prefixEnd_1717951 := by exact prefixLift 1717951
  have htrace : WordTrace (prefixWord ++ tailWord_1717951) baseStart_1717951 baseEnd_1717951 := by
    simpa [prefixWord, tailWord_1717951, baseEnd_1717951] using wordTrace_append hprefix tailTrace_1717951
  have hstable : (prefixWord ++ tailWord_1717951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717951).length < 2 ^ (prefixWord ++ tailWord_1717951).sum := by decide
  have hdescent : baseEnd_1717951 < baseStart_1717951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717978 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1717978 : Nat := 118140960795 + 1717978 * 2 ^ 59
def prefixEnd_1717978 : Nat := 4983230072969 + 3 ^ 40 * 1717978 * 2
def baseEnd_1717978 : Nat := 882148467849984636874169

theorem tailTrace_1717978 : CollatzResearch.WordTrace tailWord_1717978 prefixEnd_1717978 882148467849984636874169 := by
  unfold tailWord_1717978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664951342516647032040647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41773203580044392085441725 15664951342516647032040647)
  ·
    refine ⟨23497427013774970548060971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664951342516647032040647 23497427013774970548060971)
    ·
      refine ⟨35246140520662455822091457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23497427013774970548060971 35246140520662455822091457)
      ·
        refine ⟨26434605390496841866568593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35246140520662455822091457 26434605390496841866568593)
        ·
          refine ⟨19825954042872631399926445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26434605390496841866568593 19825954042872631399926445)
          ·
            refine ⟨7434732766077236774972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19825954042872631399926445 7434732766077236774972417)
            ·
              refine ⟨5576049574557927581229313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7434732766077236774972417 5576049574557927581229313)
              ·
                refine ⟨4182037180918445685921985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5576049574557927581229313 4182037180918445685921985)
                ·
                  refine ⟨3136527885688834264441489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182037180918445685921985 3136527885688834264441489)
                  ·
                    refine ⟨2352395914266625698331117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3136527885688834264441489 2352395914266625698331117)
                    ·
                      refine ⟨882148467849984636874169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352395914266625698331117 882148467849984636874169)
                      ·
                        rfl

theorem cell23_1717978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1717978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1717978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1717978 prefixEnd_1717978 := by exact prefixLift 1717978
  have htrace : WordTrace (prefixWord ++ tailWord_1717978) baseStart_1717978 baseEnd_1717978 := by
    simpa [prefixWord, tailWord_1717978, baseEnd_1717978] using wordTrace_append hprefix tailTrace_1717978
  have hstable : (prefixWord ++ tailWord_1717978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717978).length < 2 ^ (prefixWord ++ tailWord_1717978).sum := by decide
  have hdescent : baseEnd_1717978 < baseStart_1717978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718031 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_1718031 : Nat := 118140960795 + 1718031 * 2 ^ 59
def prefixEnd_1718031 : Nat := 4983230072969 + 3 ^ 40 * 1718031 * 2
def baseEnd_1718031 : Nat := 882175682324672929511425

theorem tailTrace_1718031 : CollatzResearch.WordTrace tailWord_1718031 prefixEnd_1718031 882175682324672929511425 := by
  unfold tailWord_1718031
  simp only [CollatzResearch.WordTrace]
  refine ⟨62661738438874578179841947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41774492292583052119894631 62661738438874578179841947)
  ·
    refine ⟨93992607658311867269762921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62661738438874578179841947 93992607658311867269762921)
    ·
      refine ⟨70494455743733900452322191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93992607658311867269762921 70494455743733900452322191)
      ·
        refine ⟨105741683615600850678483287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70494455743733900452322191 105741683615600850678483287)
        ·
          refine ⟨158612525423401276017724931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105741683615600850678483287 158612525423401276017724931)
          ·
            refine ⟨237918788135101914026587397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158612525423401276017724931 237918788135101914026587397)
            ·
              refine ⟨44609772775331608879985137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237918788135101914026587397 44609772775331608879985137)
              ·
                refine ⟨33457329581498706659988853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44609772775331608879985137 33457329581498706659988853)
                ·
                  refine ⟨3136624648265503749373955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33457329581498706659988853 3136624648265503749373955)
                  ·
                    refine ⟨4704936972398255624060933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3136624648265503749373955 4704936972398255624060933)
                    ·
                      refine ⟨882175682324672929511425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4704936972398255624060933 882175682324672929511425)
                      ·
                        rfl

theorem cell23_1718031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_1718031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718031 prefixEnd_1718031 := by exact prefixLift 1718031
  have htrace : WordTrace (prefixWord ++ tailWord_1718031) baseStart_1718031 baseEnd_1718031 := by
    simpa [prefixWord, tailWord_1718031, baseEnd_1718031] using wordTrace_append hprefix tailTrace_1718031
  have hstable : (prefixWord ++ tailWord_1718031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718031).length < 2 ^ (prefixWord ++ tailWord_1718031).sum := by decide
  have hdescent : baseEnd_1718031 < baseStart_1718031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718042 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3]
def baseStart_1718042 : Nat := 118140960795 + 1718042 * 2 ^ 59
def prefixEnd_1718042 : Nat := 4983230072969 + 3 ^ 40 * 1718042 * 2
def baseEnd_1718042 : Nat := 882181330611872386473875

theorem tailTrace_1718042 : CollatzResearch.WordTrace tailWord_1718042 prefixEnd_1718042 882181330611872386473875 := by
  unfold tailWord_1718042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15665534910458681764623095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41774759761223151372328253 15665534910458681764623095)
  ·
    refine ⟨23498302365688022646934643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15665534910458681764623095 23498302365688022646934643)
    ·
      refine ⟨35247453548532033970401965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23498302365688022646934643 35247453548532033970401965)
      ·
        refine ⟨13217795080699512738900737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35247453548532033970401965 13217795080699512738900737)
        ·
          refine ⟨9913346310524634554175553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13217795080699512738900737 9913346310524634554175553)
          ·
            refine ⟨7435009732893475915631665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913346310524634554175553 7435009732893475915631665)
            ·
              refine ⟨5576257299670106936723749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7435009732893475915631665 5576257299670106936723749)
              ·
                refine ⟨1045548243688145050635703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5576257299670106936723749 1045548243688145050635703)
                ·
                  refine ⟨1568322365532217575953555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045548243688145050635703 1568322365532217575953555)
                  ·
                    refine ⟨2352483548298326363930333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1568322365532217575953555 2352483548298326363930333)
                    ·
                      refine ⟨882181330611872386473875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352483548298326363930333 882181330611872386473875)
                      ·
                        rfl

theorem cell23_1718042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_1718042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718042 prefixEnd_1718042 := by exact prefixLift 1718042
  have htrace : WordTrace (prefixWord ++ tailWord_1718042) baseStart_1718042 baseEnd_1718042 := by
    simpa [prefixWord, tailWord_1718042, baseEnd_1718042] using wordTrace_append hprefix tailTrace_1718042
  have hstable : (prefixWord ++ tailWord_1718042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718042).length < 2 ^ (prefixWord ++ tailWord_1718042).sum := by decide
  have hdescent : baseEnd_1718042 < baseStart_1718042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718051 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1718051 : Nat := 118140960795 + 1718051 * 2 ^ 59
def prefixEnd_1718051 : Nat := 4983230072969 + 3 ^ 40 * 1718051 * 2
def baseEnd_1718051 : Nat := 882185951937762851261333

theorem tailTrace_1718051 : CollatzResearch.WordTrace tailWord_1718051 prefixEnd_1718051 882185951937762851261333 := by
  unfold tailWord_1718051
  simp only [CollatzResearch.WordTrace]
  refine ⟨62662467898802121595570007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41774978599201414397046671 62662467898802121595570007)
  ·
    refine ⟨93993701848203182393355011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62662467898802121595570007 93993701848203182393355011)
    ·
      refine ⟨140990552772304773590032517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93993701848203182393355011 140990552772304773590032517)
      ·
        refine ⟨26435728644807145048131097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140990552772304773590032517 26435728644807145048131097)
        ·
          refine ⟨19826796483605358786098323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26435728644807145048131097 19826796483605358786098323)
          ·
            refine ⟨29740194725408038179147485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19826796483605358786098323 29740194725408038179147485)
            ·
              refine ⟨11152573022028014317180307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29740194725408038179147485 11152573022028014317180307)
              ·
                refine ⟨16728859533042021475770461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11152573022028014317180307 16728859533042021475770461)
                ·
                  refine ⟨6273322324890758053413923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16728859533042021475770461 6273322324890758053413923)
                  ·
                    refine ⟨9409983487336137080120885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6273322324890758053413923 9409983487336137080120885)
                    ·
                      refine ⟨882185951937762851261333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9409983487336137080120885 882185951937762851261333)
                      ·
                        rfl

theorem cell23_1718051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1718051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718051 prefixEnd_1718051 := by exact prefixLift 1718051
  have htrace : WordTrace (prefixWord ++ tailWord_1718051) baseStart_1718051 baseEnd_1718051 := by
    simpa [prefixWord, tailWord_1718051, baseEnd_1718051] using wordTrace_append hprefix tailTrace_1718051
  have hstable : (prefixWord ++ tailWord_1718051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718051).length < 2 ^ (prefixWord ++ tailWord_1718051).sum := by decide
  have hdescent : baseEnd_1718051 < baseStart_1718051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718062 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1718062 : Nat := 118140960795 + 1718062 * 2 ^ 59
def prefixEnd_1718062 : Nat := 4983230072969 + 3 ^ 40 * 1718062 * 2
def baseEnd_1718062 : Nat := 294063866741654102741261

theorem tailTrace_1718062 : CollatzResearch.WordTrace tailWord_1718062 prefixEnd_1718062 294063866741654102741261 := by
  unfold tailWord_1718062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832858637720283809277555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41775246067841513649480293 7832858637720283809277555)
  ·
    refine ⟨11749287956580425713916333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7832858637720283809277555 11749287956580425713916333)
    ·
      refine ⟨4405982983717659642718625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11749287956580425713916333 4405982983717659642718625)
      ·
        refine ⟨3304487237788244732038969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4405982983717659642718625 3304487237788244732038969)
        ·
          refine ⟨2478365428341183549029227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304487237788244732038969 2478365428341183549029227)
          ·
            refine ⟨3717548142511775323543841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478365428341183549029227 3717548142511775323543841)
            ·
              refine ⟨2788161106883831492657881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717548142511775323543841 2788161106883831492657881)
              ·
                refine ⟨2091120830162873619493411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788161106883831492657881 2091120830162873619493411)
                ·
                  refine ⟨3136681245244310429240117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091120830162873619493411 3136681245244310429240117)
                  ·
                    refine ⟨294063866741654102741261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3136681245244310429240117 294063866741654102741261)
                    ·
                      rfl

theorem cell23_1718062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1718062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718062 prefixEnd_1718062 := by exact prefixLift 1718062
  have htrace : WordTrace (prefixWord ++ tailWord_1718062) baseStart_1718062 baseEnd_1718062 := by
    simpa [prefixWord, tailWord_1718062, baseEnd_1718062] using wordTrace_append hprefix tailTrace_1718062
  have hstable : (prefixWord ++ tailWord_1718062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718062).length < 2 ^ (prefixWord ++ tailWord_1718062).sum := by decide
  have hdescent : baseEnd_1718062 < baseStart_1718062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718065 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1718065 : Nat := 118140960795 + 1718065 * 2 ^ 59
def prefixEnd_1718065 : Nat := 4983230072969 + 3 ^ 40 * 1718065 * 2
def baseEnd_1718065 : Nat := 882193140666925796486269

theorem tailTrace_1718065 : CollatzResearch.WordTrace tailWord_1718065 prefixEnd_1718065 882193140666925796486269 := by
  unfold tailWord_1718065
  simp only [CollatzResearch.WordTrace]
  refine ⟨62662978520751401986579649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41775319013834267991053099 62662978520751401986579649)
  ·
    refine ⟨46997233890563551489934737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62662978520751401986579649 46997233890563551489934737)
    ·
      refine ⟨35247925417922663617451053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46997233890563551489934737 35247925417922663617451053)
      ·
        refine ⟨13217972031720998856544145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35247925417922663617451053 13217972031720998856544145)
        ·
          refine ⟨9913479023790749142408109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13217972031720998856544145 9913479023790749142408109)
          ·
            refine ⟨3717554633921530928403041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9913479023790749142408109 3717554633921530928403041)
            ·
              refine ⟨2788165975441148196302281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717554633921530928403041 2788165975441148196302281)
              ·
                refine ⟨2091124481580861147226711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788165975441148196302281 2091124481580861147226711)
                ·
                  refine ⟨3136686722371291720840067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091124481580861147226711 3136686722371291720840067)
                  ·
                    refine ⟨4705030083556937581260101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3136686722371291720840067 4705030083556937581260101)
                    ·
                      refine ⟨882193140666925796486269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4705030083556937581260101 882193140666925796486269)
                      ·
                        rfl

theorem cell23_1718065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1718065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718065 prefixEnd_1718065 := by exact prefixLift 1718065
  have htrace : WordTrace (prefixWord ++ tailWord_1718065) baseStart_1718065 baseEnd_1718065 := by
    simpa [prefixWord, tailWord_1718065, baseEnd_1718065] using wordTrace_append hprefix tailTrace_1718065
  have hstable : (prefixWord ++ tailWord_1718065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718065).length < 2 ^ (prefixWord ++ tailWord_1718065).sum := by decide
  have hdescent : baseEnd_1718065 < baseStart_1718065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718131 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 4, 6]
def baseStart_1718131 : Nat := 118140960795 + 1718131 * 2 ^ 59
def prefixEnd_1718131 : Nat := 4983230072969 + 3 ^ 40 * 1718131 * 2
def baseEnd_1718131 : Nat := 294075676796707512753655

theorem tailTrace_1718131 : CollatzResearch.WordTrace tailWord_1718131 prefixEnd_1718131 294075676796707512753655 := by
  unfold tailWord_1718131
  simp only [CollatzResearch.WordTrace]
  refine ⟨62665385738512295258482247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41776923825674863505654831 62665385738512295258482247)
  ·
    refine ⟨93998078607768442887723371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62665385738512295258482247 93998078607768442887723371)
    ·
      refine ⟨140997117911652664331585057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93998078607768442887723371 140997117911652664331585057)
      ·
        refine ⟨105747838433739498248688793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140997117911652664331585057 105747838433739498248688793)
        ·
          refine ⟨79310878825304623686516595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105747838433739498248688793 79310878825304623686516595)
          ·
            refine ⟨118966318237956935529774893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79310878825304623686516595 118966318237956935529774893)
            ·
              refine ⟨44612369339233850823665585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118966318237956935529774893 44612369339233850823665585)
              ·
                refine ⟨33459277004425388117749189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44612369339233850823665585 33459277004425388117749189)
                ·
                  refine ⟨6273614438329760272077973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33459277004425388117749189 6273614438329760272077973)
                  ·
                    refine ⟨294075676796707512753655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6273614438329760272077973 294075676796707512753655)
                    ·
                      rfl

theorem cell23_1718131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_1718131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718131 prefixEnd_1718131 := by exact prefixLift 1718131
  have htrace : WordTrace (prefixWord ++ tailWord_1718131) baseStart_1718131 baseEnd_1718131 := by
    simpa [prefixWord, tailWord_1718131, baseEnd_1718131] using wordTrace_append hprefix tailTrace_1718131
  have hstable : (prefixWord ++ tailWord_1718131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718131).length < 2 ^ (prefixWord ++ tailWord_1718131).sum := by decide
  have hdescent : baseEnd_1718131 < baseStart_1718131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718166 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1718166 : Nat := 118140960795 + 1718166 * 2 ^ 59
def prefixEnd_1718166 : Nat := 4983230072969 + 3 ^ 40 * 1718166 * 2
def baseEnd_1718166 : Nat := 882245002213029901323305

theorem tailTrace_1718166 : CollatzResearch.WordTrace tailWord_1718166 prefixEnd_1718166 882245002213029901323305 := by
  unfold tailWord_1718166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916666393336593514750397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41777774862256997490670901 3916666393336593514750397)
  ·
    refine ⟨1468749897501222568031399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3916666393336593514750397 1468749897501222568031399)
    ·
      refine ⟨2203124846251833852047099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468749897501222568031399 2203124846251833852047099)
      ·
        refine ⟨3304687269377750778070649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203124846251833852047099 3304687269377750778070649)
        ·
          refine ⟨2478515452033313083552987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304687269377750778070649 2478515452033313083552987)
          ·
            refine ⟨3717773178049969625329481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478515452033313083552987 3717773178049969625329481)
            ·
              refine ⟨2788329883537477218997111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717773178049969625329481 2788329883537477218997111)
              ·
                refine ⟨4182494825306215828495667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788329883537477218997111 4182494825306215828495667)
                ·
                  refine ⟨6273742237959323742743501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182494825306215828495667 6273742237959323742743501)
                  ·
                    refine ⟨2352653339234746403528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6273742237959323742743501 2352653339234746403528813)
                    ·
                      refine ⟨882245002213029901323305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352653339234746403528813 882245002213029901323305)
                      ·
                        rfl

theorem cell23_1718166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1718166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718166 prefixEnd_1718166 := by exact prefixLift 1718166
  have htrace : WordTrace (prefixWord ++ tailWord_1718166) baseStart_1718166 baseEnd_1718166 := by
    simpa [prefixWord, tailWord_1718166, baseEnd_1718166] using wordTrace_append hprefix tailTrace_1718166
  have hstable : (prefixWord ++ tailWord_1718166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718166).length < 2 ^ (prefixWord ++ tailWord_1718166).sum := by decide
  have hdescent : baseEnd_1718166 < baseStart_1718166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718172 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1718172 : Nat := 118140960795 + 1718172 * 2 ^ 59
def prefixEnd_1718172 : Nat := 4983230072969 + 3 ^ 40 * 1718172 * 2
def baseEnd_1718172 : Nat := 882248083096956877848277

theorem tailTrace_1718172 : CollatzResearch.WordTrace tailWord_1718172 prefixEnd_1718172 882248083096956877848277 := by
  unfold tailWord_1718172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31333440565681879630362385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41777920754242506173816513 31333440565681879630362385)
  ·
    refine ⟨23500080424261409722771789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31333440565681879630362385 23500080424261409722771789)
    ·
      refine ⟨8812530159098028646039421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23500080424261409722771789 8812530159098028646039421)
      ·
        refine ⟨3304698809661760742264783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8812530159098028646039421 3304698809661760742264783)
        ·
          refine ⟨4957048214492641113397175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304698809661760742264783 4957048214492641113397175)
          ·
            refine ⟨7435572321738961670095763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957048214492641113397175 7435572321738961670095763)
            ·
              refine ⟨11153358482608442505143645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435572321738961670095763 11153358482608442505143645)
              ·
                refine ⟨4182509430978165939428867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11153358482608442505143645 4182509430978165939428867)
                ·
                  refine ⟨6273764146467248909143301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182509430978165939428867 6273764146467248909143301)
                  ·
                    refine ⟨1176330777462609170464369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273764146467248909143301 1176330777462609170464369)
                    ·
                      refine ⟨882248083096956877848277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176330777462609170464369 882248083096956877848277)
                      ·
                        rfl

theorem cell23_1718172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1718172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718172 prefixEnd_1718172 := by exact prefixLift 1718172
  have htrace : WordTrace (prefixWord ++ tailWord_1718172) baseStart_1718172 baseEnd_1718172 := by
    simpa [prefixWord, tailWord_1718172, baseEnd_1718172] using wordTrace_append hprefix tailTrace_1718172
  have hstable : (prefixWord ++ tailWord_1718172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718172).length < 2 ^ (prefixWord ++ tailWord_1718172).sum := by decide
  have hdescent : baseEnd_1718172 < baseStart_1718172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718188 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_1718188 : Nat := 118140960795 + 1718188 * 2 ^ 59
def prefixEnd_1718188 : Nat := 4983230072969 + 3 ^ 40 * 1718188 * 2
def baseEnd_1718188 : Nat := 882256298787428815248203

theorem tailTrace_1718188 : CollatzResearch.WordTrace tailWord_1718188 prefixEnd_1718188 882256298787428815248203 := by
  unfold tailWord_1718188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31333732349652896996653609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41778309799537195995538145 31333732349652896996653609)
  ·
    refine ⟨23500299262239672747490207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31333732349652896996653609 23500299262239672747490207)
    ·
      refine ⟨35250448893359509121235311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23500299262239672747490207 35250448893359509121235311)
      ·
        refine ⟨52875673340039263681852967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35250448893359509121235311 52875673340039263681852967)
        ·
          refine ⟨79313510010058895522779451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52875673340039263681852967 79313510010058895522779451)
          ·
            refine ⟨118970265015088343284169177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79313510010058895522779451 118970265015088343284169177)
            ·
              refine ⟨89227698761316257463126883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118970265015088343284169177 89227698761316257463126883)
              ·
                refine ⟨133841548141974386194690325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89227698761316257463126883 133841548141974386194690325)
                ·
                  refine ⟨6273822569155049352876109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133841548141974386194690325 6273822569155049352876109)
                  ·
                    refine ⟨2352683463433143507328541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6273822569155049352876109 2352683463433143507328541)
                    ·
                      refine ⟨882256298787428815248203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352683463433143507328541 882256298787428815248203)
                      ·
                        rfl

theorem cell23_1718188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_1718188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718188 prefixEnd_1718188 := by exact prefixLift 1718188
  have htrace : WordTrace (prefixWord ++ tailWord_1718188) baseStart_1718188 baseEnd_1718188 := by
    simpa [prefixWord, tailWord_1718188, baseEnd_1718188] using wordTrace_append hprefix tailTrace_1718188
  have hstable : (prefixWord ++ tailWord_1718188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718188).length < 2 ^ (prefixWord ++ tailWord_1718188).sum := by decide
  have hdescent : baseEnd_1718188 < baseStart_1718188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718195 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 5]
def baseStart_1718195 : Nat := 118140960795 + 1718195 * 2 ^ 59
def prefixEnd_1718195 : Nat := 4983230072969 + 3 ^ 40 * 1718195 * 2
def baseEnd_1718195 : Nat := 98028877016890031984519

theorem tailTrace_1718195 : CollatzResearch.WordTrace tailWord_1718195 prefixEnd_1718195 98028877016890031984519 := by
  unfold tailWord_1718195
  simp only [CollatzResearch.WordTrace]
  refine ⟨62667720010280434188812039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41778480006853622792541359 62667720010280434188812039)
  ·
    refine ⟨94001580015420651283218059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62667720010280434188812039 94001580015420651283218059)
    ·
      refine ⟨141002370023130976924827089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94001580015420651283218059 141002370023130976924827089)
      ·
        refine ⟨105751777517348232693620317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141002370023130976924827089 105751777517348232693620317)
        ·
          refine ⟨39656916569005587260107619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105751777517348232693620317 39656916569005587260107619)
          ·
            refine ⟨59485374853508380890161429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39656916569005587260107619 59485374853508380890161429)
            ·
              refine ⟨2788376946258205354226317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59485374853508380890161429 2788376946258205354226317)
              ·
                refine ⟨1045641354846827007834869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2788376946258205354226317 1045641354846827007834869)
                ·
                  refine ⟨98028877016890031984519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1045641354846827007834869 98028877016890031984519)
                  ·
                    rfl

theorem cell23_1718195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 5].length) (baseStart_1718195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718195 prefixEnd_1718195 := by exact prefixLift 1718195
  have htrace : WordTrace (prefixWord ++ tailWord_1718195) baseStart_1718195 baseEnd_1718195 := by
    simpa [prefixWord, tailWord_1718195, baseEnd_1718195] using wordTrace_append hprefix tailTrace_1718195
  have hstable : (prefixWord ++ tailWord_1718195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718195).length < 2 ^ (prefixWord ++ tailWord_1718195).sum := by decide
  have hdescent : baseEnd_1718195 < baseStart_1718195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718205 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1718205 : Nat := 118140960795 + 1718205 * 2 ^ 59
def prefixEnd_1718205 : Nat := 4983230072969 + 3 ^ 40 * 1718205 * 2
def baseEnd_1718205 : Nat := 882265027958555248735625

theorem tailTrace_1718205 : CollatzResearch.WordTrace tailWord_1718205 prefixEnd_1718205 882265027958555248735625 := by
  unfold tailWord_1718205
  simp only [CollatzResearch.WordTrace]
  refine ⟨62668084740244205896676069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41778723160162803931117379 62668084740244205896676069)
  ·
    refine ⟨11750265888795788605626763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62668084740244205896676069 11750265888795788605626763)
    ·
      refine ⟨17625398833193682908440145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750265888795788605626763 17625398833193682908440145)
      ·
        refine ⟨13219049124895262181330109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17625398833193682908440145 13219049124895262181330109)
        ·
          refine ⟨4957143421835723317998791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13219049124895262181330109 4957143421835723317998791)
          ·
            refine ⟨7435715132753584976998187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957143421835723317998791 7435715132753584976998187)
            ·
              refine ⟨11153572699130377465497281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435715132753584976998187 11153572699130377465497281)
              ·
                refine ⟨8365179524347783099122961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11153572699130377465497281 8365179524347783099122961)
                ·
                  refine ⟨6273884643260837324342221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365179524347783099122961 6273884643260837324342221)
                  ·
                    refine ⟨2352706741222813996628333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6273884643260837324342221 2352706741222813996628333)
                    ·
                      refine ⟨882265027958555248735625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352706741222813996628333 882265027958555248735625)
                      ·
                        rfl

theorem cell23_1718205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1718205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718205 prefixEnd_1718205 := by exact prefixLift 1718205
  have htrace : WordTrace (prefixWord ++ tailWord_1718205) baseStart_1718205 baseEnd_1718205 := by
    simpa [prefixWord, tailWord_1718205, baseEnd_1718205] using wordTrace_append hprefix tailTrace_1718205
  have hstable : (prefixWord ++ tailWord_1718205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718205).length < 2 ^ (prefixWord ++ tailWord_1718205).sum := by decide
  have hdescent : baseEnd_1718205 < baseStart_1718205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718206 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_1718206 : Nat := 118140960795 + 1718206 * 2 ^ 59
def prefixEnd_1718206 : Nat := 4983230072969 + 3 ^ 40 * 1718206 * 2
def baseEnd_1718206 : Nat := 882265541439209744823121

theorem tailTrace_1718206 : CollatzResearch.WordTrace tailWord_1718206 prefixEnd_1718206 882265541439209744823121 := by
  unfold tailWord_1718206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833515151655072883432809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41778747475493722044974981 7833515151655072883432809)
  ·
    refine ⟨5875136363741304662574607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7833515151655072883432809 5875136363741304662574607)
    ·
      refine ⟨8812704545611956993861911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5875136363741304662574607 8812704545611956993861911)
      ·
        refine ⟨13219056818417935490792867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812704545611956993861911 13219056818417935490792867)
        ·
          refine ⟨19828585227626903236189301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13219056818417935490792867 19828585227626903236189301)
          ·
            refine ⟨1858929865090022178392747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19828585227626903236189301 1858929865090022178392747)
            ·
              refine ⟨2788394797635033267589121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858929865090022178392747 2788394797635033267589121)
              ·
                refine ⟨2091296098226274950691841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788394797635033267589121 2091296098226274950691841)
                ·
                  refine ⟨1568472073669706213018881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2091296098226274950691841 1568472073669706213018881)
                  ·
                    refine ⟨1176354055252279659764161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1568472073669706213018881 1176354055252279659764161)
                    ·
                      refine ⟨882265541439209744823121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176354055252279659764161 882265541439209744823121)
                      ·
                        rfl

theorem cell23_1718206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_1718206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718206 prefixEnd_1718206 := by exact prefixLift 1718206
  have htrace : WordTrace (prefixWord ++ tailWord_1718206) baseStart_1718206 baseEnd_1718206 := by
    simpa [prefixWord, tailWord_1718206, baseEnd_1718206] using wordTrace_append hprefix tailTrace_1718206
  have hstable : (prefixWord ++ tailWord_1718206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718206).length < 2 ^ (prefixWord ++ tailWord_1718206).sum := by decide
  have hdescent : baseEnd_1718206 < baseStart_1718206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718208 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_1718208 : Nat := 118140960795 + 1718208 * 2 ^ 59
def prefixEnd_1718208 : Nat := 4983230072969 + 3 ^ 40 * 1718208 * 2
def baseEnd_1718208 : Nat := 294088856133506245666037

theorem tailTrace_1718208 : CollatzResearch.WordTrace tailWord_1718208 prefixEnd_1718208 294088856133506245666037 := by
  unfold tailWord_1718208
  simp only [CollatzResearch.WordTrace]
  refine ⟨31334097079616668704517639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41778796106155558272690185 31334097079616668704517639)
  ·
    refine ⟨47001145619425003056776459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31334097079616668704517639 47001145619425003056776459)
    ·
      refine ⟨70501718429137504585164689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47001145619425003056776459 70501718429137504585164689)
      ·
        refine ⟨52876288821853128438873517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70501718429137504585164689 52876288821853128438873517)
        ·
          refine ⟨19828608308194923164577569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52876288821853128438873517 19828608308194923164577569)
          ·
            refine ⟨14871456231146192373433177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19828608308194923164577569 14871456231146192373433177)
            ·
              refine ⟨11153592173359644280074883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14871456231146192373433177 11153592173359644280074883)
              ·
                refine ⟨16730388260039466420112325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153592173359644280074883 16730388260039466420112325)
                ·
                  refine ⟨3136947798757399953771061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16730388260039466420112325 3136947798757399953771061)
                  ·
                    refine ⟨294088856133506245666037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3136947798757399953771061 294088856133506245666037)
                    ·
                      rfl

theorem cell23_1718208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_1718208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718208 prefixEnd_1718208 := by exact prefixLift 1718208
  have htrace : WordTrace (prefixWord ++ tailWord_1718208) baseStart_1718208 baseEnd_1718208 := by
    simpa [prefixWord, tailWord_1718208, baseEnd_1718208] using wordTrace_append hprefix tailTrace_1718208
  have hstable : (prefixWord ++ tailWord_1718208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718208).length < 2 ^ (prefixWord ++ tailWord_1718208).sum := by decide
  have hdescent : baseEnd_1718208 < baseStart_1718208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718218 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1718218 : Nat := 118140960795 + 1718218 * 2 ^ 59
def prefixEnd_1718218 : Nat := 4983230072969 + 3 ^ 40 * 1718218 * 2
def baseEnd_1718218 : Nat := 882271703207063697873065

theorem tailTrace_1718218 : CollatzResearch.WordTrace tailWord_1718218 prefixEnd_1718218 882271703207063697873065 := by
  unfold tailWord_1718218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667139722299277279224827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41779039259464739411266205 15667139722299277279224827)
  ·
    refine ⟨23500709583448915918837241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15667139722299277279224827 23500709583448915918837241)
    ·
      refine ⟨17625532187586686939127931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23500709583448915918837241 17625532187586686939127931)
      ·
        refine ⟨26438298281380030408691897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625532187586686939127931 26438298281380030408691897)
        ·
          refine ⟨19828723711035022806518923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26438298281380030408691897 19828723711035022806518923)
          ·
            refine ⟨29743085566552534209778385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19828723711035022806518923 29743085566552534209778385)
            ·
              refine ⟨22307314174914400657333789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29743085566552534209778385 22307314174914400657333789)
              ·
                refine ⟨8365242815592900246500171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22307314174914400657333789 8365242815592900246500171)
                ·
                  refine ⟨12547864223389350369750257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365242815592900246500171 12547864223389350369750257)
                  ·
                    refine ⟨9410898167542012777312693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12547864223389350369750257 9410898167542012777312693)
                    ·
                      refine ⟨882271703207063697873065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9410898167542012777312693 882271703207063697873065)
                      ·
                        rfl

theorem cell23_1718218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1718218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718218 prefixEnd_1718218 := by exact prefixLift 1718218
  have htrace : WordTrace (prefixWord ++ tailWord_1718218) baseStart_1718218 baseEnd_1718218 := by
    simpa [prefixWord, tailWord_1718218, baseEnd_1718218] using wordTrace_append hprefix tailTrace_1718218
  have hstable : (prefixWord ++ tailWord_1718218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718218).length < 2 ^ (prefixWord ++ tailWord_1718218).sum := by decide
  have hdescent : baseEnd_1718218 < baseStart_1718218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718248 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1718248 : Nat := 118140960795 + 1718248 * 2 ^ 59
def prefixEnd_1718248 : Nat := 4983230072969 + 3 ^ 40 * 1718248 * 2
def baseEnd_1718248 : Nat := 882287107626698580497927

theorem tailTrace_1718248 : CollatzResearch.WordTrace tailWord_1718248 prefixEnd_1718248 882287107626698580497927 := by
  unfold tailWord_1718248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31334826539544212120245699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41779768719392282826994265 31334826539544212120245699)
  ·
    refine ⟨47002239809316318180368549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31334826539544212120245699 47002239809316318180368549)
    ·
      refine ⟨8812919964246809658819103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47002239809316318180368549 8812919964246809658819103)
      ·
        refine ⟨13219379946370214488228655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812919964246809658819103 13219379946370214488228655)
        ·
          refine ⟨19829069919555321732342983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13219379946370214488228655 19829069919555321732342983)
          ·
            refine ⟨29743604879332982598514475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19829069919555321732342983 29743604879332982598514475)
            ·
              refine ⟨44615407318999473897771713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29743604879332982598514475 44615407318999473897771713)
              ·
                refine ⟨33461555489249605423328785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44615407318999473897771713 33461555489249605423328785)
                ·
                  refine ⟨25096166616937204067496589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33461555489249605423328785 25096166616937204067496589)
                  ·
                    refine ⟨9411062481351451525311221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25096166616937204067496589 9411062481351451525311221)
                    ·
                      refine ⟨882287107626698580497927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9411062481351451525311221 882287107626698580497927)
                      ·
                        rfl

theorem cell23_1718248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1718248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718248 prefixEnd_1718248 := by exact prefixLift 1718248
  have htrace : WordTrace (prefixWord ++ tailWord_1718248) baseStart_1718248 baseEnd_1718248 := by
    simpa [prefixWord, tailWord_1718248, baseEnd_1718248] using wordTrace_append hprefix tailTrace_1718248
  have hstable : (prefixWord ++ tailWord_1718248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718248).length < 2 ^ (prefixWord ++ tailWord_1718248).sum := by decide
  have hdescent : baseEnd_1718248 < baseStart_1718248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718265 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1718265 : Nat := 118140960795 + 1718265 * 2 ^ 59
def prefixEnd_1718265 : Nat := 4983230072969 + 3 ^ 40 * 1718265 * 2
def baseEnd_1718265 : Nat := 882295836797825013985349

theorem tailTrace_1718265 : CollatzResearch.WordTrace tailWord_1718265 prefixEnd_1718265 882295836797825013985349 := by
  unfold tailWord_1718265
  simp only [CollatzResearch.WordTrace]
  refine ⟨62670273120026836143860249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41780182080017890762573499 62670273120026836143860249)
  ·
    refine ⟨47002704840020127107895187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62670273120026836143860249 47002704840020127107895187)
    ·
      refine ⟨70504057260030190661842781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47002704840020127107895187 70504057260030190661842781)
      ·
        refine ⟨26439021472511321498191043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70504057260030190661842781 26439021472511321498191043)
        ·
          refine ⟨39658532208766982247286565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26439021472511321498191043 39658532208766982247286565)
          ·
            refine ⟨7435974789143809171366231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39658532208766982247286565 7435974789143809171366231)
            ·
              refine ⟨11153962183715713757049347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435974789143809171366231 11153962183715713757049347)
              ·
                refine ⟨16730943275573570635574021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153962183715713757049347 16730943275573570635574021)
                ·
                  refine ⟨3137051864170044494170129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16730943275573570635574021 3137051864170044494170129)
                  ·
                    refine ⟨2352788898127533370627597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137051864170044494170129 2352788898127533370627597)
                    ·
                      refine ⟨882295836797825013985349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352788898127533370627597 882295836797825013985349)
                      ·
                        rfl

theorem cell23_1718265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1718265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718265 prefixEnd_1718265 := by exact prefixLift 1718265
  have htrace : WordTrace (prefixWord ++ tailWord_1718265) baseStart_1718265 baseEnd_1718265 := by
    simpa [prefixWord, tailWord_1718265, baseEnd_1718265] using wordTrace_append hprefix tailTrace_1718265
  have hstable : (prefixWord ++ tailWord_1718265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718265).length < 2 ^ (prefixWord ++ tailWord_1718265).sum := by decide
  have hdescent : baseEnd_1718265 < baseStart_1718265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718268 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 8]
def baseStart_1718268 : Nat := 118140960795 + 1718268 * 2 ^ 59
def prefixEnd_1718268 : Nat := 4983230072969 + 3 ^ 40 * 1718268 * 2
def baseEnd_1718268 : Nat := 98033041915532055805315

theorem tailTrace_1718268 : CollatzResearch.WordTrace tailWord_1718268 prefixEnd_1718268 98033041915532055805315 := by
  unfold tailWord_1718268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31335191269507983828109729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41780255026010645104146305 31335191269507983828109729)
  ·
    refine ⟨23501393452130987871082297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31335191269507983828109729 23501393452130987871082297)
    ·
      refine ⟨17626045089098240903311723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23501393452130987871082297 17626045089098240903311723)
      ·
        refine ⟨26439067633647361354967585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17626045089098240903311723 26439067633647361354967585)
        ·
          refine ⟨19829300725235521016225689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26439067633647361354967585 19829300725235521016225689)
          ·
            refine ⟨14871975543926640762169267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19829300725235521016225689 14871975543926640762169267)
            ·
              refine ⟨22307963315889961143253901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14871975543926640762169267 22307963315889961143253901)
              ·
                refine ⟨8365486243458735428720213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22307963315889961143253901 8365486243458735428720213)
                ·
                  refine ⟨98033041915532055805315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8365486243458735428720213 98033041915532055805315)
                  ·
                    rfl

theorem cell23_1718268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_1718268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718268 prefixEnd_1718268 := by exact prefixLift 1718268
  have htrace : WordTrace (prefixWord ++ tailWord_1718268) baseStart_1718268 baseEnd_1718268 := by
    simpa [prefixWord, tailWord_1718268, baseEnd_1718268] using wordTrace_append hprefix tailTrace_1718268
  have hstable : (prefixWord ++ tailWord_1718268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718268).length < 2 ^ (prefixWord ++ tailWord_1718268).sum := by decide
  have hdescent : baseEnd_1718268 < baseStart_1718268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718335 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1718335 : Nat := 118140960795 + 1718335 * 2 ^ 59
def prefixEnd_1718335 : Nat := 4983230072969 + 3 ^ 40 * 1718335 * 2
def baseEnd_1718335 : Nat := 882331780443639740110027

theorem tailTrace_1718335 : CollatzResearch.WordTrace tailWord_1718335 prefixEnd_1718335 882331780443639740110027 := by
  unfold tailWord_1718335
  simp only [CollatzResearch.WordTrace]
  refine ⟨62672826229773238098908459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41781884153182158732605639 62672826229773238098908459)
  ·
    refine ⟨94009239344659857148362689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62672826229773238098908459 94009239344659857148362689)
    ·
      refine ⟨70506929508494892861272017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94009239344659857148362689 70506929508494892861272017)
      ·
        refine ⟨52880197131371169645954013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70506929508494892861272017 52880197131371169645954013)
        ·
          refine ⟨19830073924264188617232755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52880197131371169645954013 19830073924264188617232755)
          ·
            refine ⟨29745110886396282925849133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19830073924264188617232755 29745110886396282925849133)
            ·
              refine ⟨11154416582398606097193425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29745110886396282925849133 11154416582398606097193425)
              ·
                refine ⟨8365812436798954572895069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11154416582398606097193425 8365812436798954572895069)
                ·
                  refine ⟨3137179663799607964835651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8365812436798954572895069 3137179663799607964835651)
                  ·
                    refine ⟨4705769495699411947253477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3137179663799607964835651 4705769495699411947253477)
                    ·
                      refine ⟨882331780443639740110027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4705769495699411947253477 882331780443639740110027)
                      ·
                        rfl

theorem cell23_1718335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1718335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718335 prefixEnd_1718335 := by exact prefixLift 1718335
  have htrace : WordTrace (prefixWord ++ tailWord_1718335) baseStart_1718335 baseEnd_1718335 := by
    simpa [prefixWord, tailWord_1718335, baseEnd_1718335] using wordTrace_append hprefix tailTrace_1718335
  have hstable : (prefixWord ++ tailWord_1718335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718335).length < 2 ^ (prefixWord ++ tailWord_1718335).sum := by decide
  have hdescent : baseEnd_1718335 < baseStart_1718335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718342 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1718342 : Nat := 118140960795 + 1718342 * 2 ^ 59
def prefixEnd_1718342 : Nat := 4983230072969 + 3 ^ 40 * 1718342 * 2
def baseEnd_1718342 : Nat := 882335374808221212722495

theorem tailTrace_1718342 : CollatzResearch.WordTrace tailWord_1718342 prefixEnd_1718342 882335374808221212722495 := by
  unfold tailWord_1718342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958533798148371196700415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41782054360498585529608853 1958533798148371196700415)
  ·
    refine ⟨2937800697222556795050623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1958533798148371196700415 2937800697222556795050623)
    ·
      refine ⟨4406701045833835192575935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2937800697222556795050623 4406701045833835192575935)
      ·
        refine ⟨6610051568750752788863903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4406701045833835192575935 6610051568750752788863903)
        ·
          refine ⟨9915077353126129183295855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610051568750752788863903 9915077353126129183295855)
          ·
            refine ⟨14872616029689193774943783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915077353126129183295855 14872616029689193774943783)
            ·
              refine ⟨22308924044533790662415675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14872616029689193774943783 22308924044533790662415675)
              ·
                refine ⟨33463386066800685993623513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22308924044533790662415675 33463386066800685993623513)
                ·
                  refine ⟨25097539550100514495217635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33463386066800685993623513 25097539550100514495217635)
                  ·
                    refine ⟨37646309325150771742826453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25097539550100514495217635 37646309325150771742826453)
                    ·
                      refine ⟨882335374808221212722495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37646309325150771742826453 882335374808221212722495)
                      ·
                        rfl

theorem cell23_1718342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1718342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718342 prefixEnd_1718342 := by exact prefixLift 1718342
  have htrace : WordTrace (prefixWord ++ tailWord_1718342) baseStart_1718342 baseEnd_1718342 := by
    simpa [prefixWord, tailWord_1718342, baseEnd_1718342] using wordTrace_append hprefix tailTrace_1718342
  have hstable : (prefixWord ++ tailWord_1718342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718342).length < 2 ^ (prefixWord ++ tailWord_1718342).sum := by decide
  have hdescent : baseEnd_1718342 < baseStart_1718342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718345 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_1718345 : Nat := 118140960795 + 1718345 * 2 ^ 59
def prefixEnd_1718345 : Nat := 4983230072969 + 3 ^ 40 * 1718345 * 2
def baseEnd_1718345 : Nat := 294112305083394900328327

theorem tailTrace_1718345 : CollatzResearch.WordTrace tailWord_1718345 prefixEnd_1718345 294112305083394900328327 := by
  unfold tailWord_1718345
  simp only [CollatzResearch.WordTrace]
  refine ⟨62673190959737009806772489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41782127306491339871181659 62673190959737009806772489)
  ·
    refine ⟨47004893219802757355079367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62673190959737009806772489 47004893219802757355079367)
    ·
      refine ⟨70507339829704136032619051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47004893219802757355079367 70507339829704136032619051)
      ·
        refine ⟨105761009744556204048928577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70507339829704136032619051 105761009744556204048928577)
        ·
          refine ⟨79320757308417153036696433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105761009744556204048928577 79320757308417153036696433)
          ·
            refine ⟨59490567981312864777522325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79320757308417153036696433 59490567981312864777522325)
            ·
              refine ⟨2788620374124040536446359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59490567981312864777522325 2788620374124040536446359)
              ·
                refine ⟨4182930561186060804669539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788620374124040536446359 4182930561186060804669539)
                ·
                  refine ⟨6274395841779091207004309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182930561186060804669539 6274395841779091207004309)
                  ·
                    refine ⟨294112305083394900328327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6274395841779091207004309 294112305083394900328327)
                    ·
                      rfl

theorem cell23_1718345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_1718345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718345 prefixEnd_1718345 := by exact prefixLift 1718345
  have htrace : WordTrace (prefixWord ++ tailWord_1718345) baseStart_1718345 baseEnd_1718345 := by
    simpa [prefixWord, tailWord_1718345, baseEnd_1718345] using wordTrace_append hprefix tailTrace_1718345
  have hstable : (prefixWord ++ tailWord_1718345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718345).length < 2 ^ (prefixWord ++ tailWord_1718345).sum := by decide
  have hdescent : baseEnd_1718345 < baseStart_1718345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718355 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3]
def baseStart_1718355 : Nat := 118140960795 + 1718355 * 2 ^ 59
def prefixEnd_1718355 : Nat := 4983230072969 + 3 ^ 40 * 1718355 * 2
def baseEnd_1718355 : Nat := 882342050056729661859935

theorem tailTrace_1718355 : CollatzResearch.WordTrace tailWord_1718355 prefixEnd_1718355 882342050056729661859935 := by
  unfold tailWord_1718355
  simp only [CollatzResearch.WordTrace]
  refine ⟨62673555689700781514636519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41782370459800521009757679 62673555689700781514636519)
  ·
    refine ⟨94010333534551172271954779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62673555689700781514636519 94010333534551172271954779)
    ·
      refine ⟨141015500301826758407932169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94010333534551172271954779 141015500301826758407932169)
      ·
        refine ⟨105761625226370068805949127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141015500301826758407932169 105761625226370068805949127)
        ·
          refine ⟨158642437839555103208923691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105761625226370068805949127 158642437839555103208923691)
          ·
            refine ⟨237963656759332654813385537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158642437839555103208923691 237963656759332654813385537)
            ·
              refine ⟨178472742569499491110039153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237963656759332654813385537 178472742569499491110039153)
              ·
                refine ⟨133854556927124618332529365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178472742569499491110039153 133854556927124618332529365)
                ·
                  refine ⟨3137216177979483242168657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133854556927124618332529365 3137216177979483242168657)
                  ·
                    refine ⟨2352912133484612431626493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3137216177979483242168657 2352912133484612431626493)
                    ·
                      refine ⟨882342050056729661859935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2352912133484612431626493 882342050056729661859935)
                      ·
                        rfl

theorem cell23_1718355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_1718355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718355 prefixEnd_1718355 := by exact prefixLift 1718355
  have htrace : WordTrace (prefixWord ++ tailWord_1718355) baseStart_1718355 baseEnd_1718355 := by
    simpa [prefixWord, tailWord_1718355, baseEnd_1718355] using wordTrace_append hprefix tailTrace_1718355
  have hstable : (prefixWord ++ tailWord_1718355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718355).length < 2 ^ (prefixWord ++ tailWord_1718355).sum := by decide
  have hdescent : baseEnd_1718355 < baseStart_1718355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718386 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_1718386 : Nat := 118140960795 + 1718386 * 2 ^ 59
def prefixEnd_1718386 : Nat := 4983230072969 + 3 ^ 40 * 1718386 * 2
def baseEnd_1718386 : Nat := 882357967957019040572293

theorem tailTrace_1718386 : CollatzResearch.WordTrace tailWord_1718386 prefixEnd_1718386 882357967957019040572293 := by
  unfold tailWord_1718386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668671588147118452253753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41783124235058982539343341 15668671588147118452253753)
  ·
    refine ⟨11751503691110338839190315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15668671588147118452253753 11751503691110338839190315)
    ·
      refine ⟨17627255536665508258785473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11751503691110338839190315 17627255536665508258785473)
      ·
        refine ⟨13220441652499131194089105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17627255536665508258785473 13220441652499131194089105)
        ·
          refine ⟨9915331239374348395566829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13220441652499131194089105 9915331239374348395566829)
          ·
            refine ⟨3718249214765380648337561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9915331239374348395566829 3718249214765380648337561)
            ·
              refine ⟨2788686911074035486253171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718249214765380648337561 2788686911074035486253171)
              ·
                refine ⟨4183030366611053229379757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788686911074035486253171 4183030366611053229379757)
                ·
                  refine ⟨1568636387479144961017409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4183030366611053229379757 1568636387479144961017409)
                  ·
                    refine ⟨1176477290609358720763057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1568636387479144961017409 1176477290609358720763057)
                    ·
                      refine ⟨882357967957019040572293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176477290609358720763057 882357967957019040572293)
                      ·
                        rfl

theorem cell23_1718386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_1718386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718386 prefixEnd_1718386 := by exact prefixLift 1718386
  have htrace : WordTrace (prefixWord ++ tailWord_1718386) baseStart_1718386 baseEnd_1718386 := by
    simpa [prefixWord, tailWord_1718386, baseEnd_1718386] using wordTrace_append hprefix tailTrace_1718386
  have hstable : (prefixWord ++ tailWord_1718386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718386).length < 2 ^ (prefixWord ++ tailWord_1718386).sum := by decide
  have hdescent : baseEnd_1718386 < baseStart_1718386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718453 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1718453 : Nat := 118140960795 + 1718453 * 2 ^ 59
def prefixEnd_1718453 : Nat := 4983230072969 + 3 ^ 40 * 1718453 * 2
def baseEnd_1718453 : Nat := 882392371160870278434485

theorem tailTrace_1718453 : CollatzResearch.WordTrace tailWord_1718453 prefixEnd_1718453 882392371160870278434485 := by
  unfold tailWord_1718453
  simp only [CollatzResearch.WordTrace]
  refine ⟨62677130043345744251704013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41784753362230496167802675 62677130043345744251704013)
  ·
    refine ⟨23503923766254654094389005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62677130043345744251704013 23503923766254654094389005)
    ·
      refine ⟨8813971412345495285395877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23503923766254654094389005 8813971412345495285395877)
      ·
        refine ⟨1652619639814780366011727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8813971412345495285395877 1652619639814780366011727)
        ·
          refine ⟨2478929459722170549017591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652619639814780366011727 2478929459722170549017591)
          ·
            refine ⟨3718394189583255823526387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478929459722170549017591 3718394189583255823526387)
            ·
              refine ⟨5577591284374883735289581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718394189583255823526387 5577591284374883735289581)
              ·
                refine ⟨2091596731640581400733593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5577591284374883735289581 2091596731640581400733593)
                ·
                  refine ⟨1568697548730436050550195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2091596731640581400733593 1568697548730436050550195)
                  ·
                    refine ⟨2353046323095654075825293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1568697548730436050550195 2353046323095654075825293)
                    ·
                      refine ⟨882392371160870278434485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2353046323095654075825293 882392371160870278434485)
                      ·
                        rfl

theorem cell23_1718453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1718453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718453 prefixEnd_1718453 := by exact prefixLift 1718453
  have htrace : WordTrace (prefixWord ++ tailWord_1718453) baseStart_1718453 baseEnd_1718453 := by
    simpa [prefixWord, tailWord_1718453, baseEnd_1718453] using wordTrace_append hprefix tailTrace_1718453
  have hstable : (prefixWord ++ tailWord_1718453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718453).length < 2 ^ (prefixWord ++ tailWord_1718453).sum := by decide
  have hdescent : baseEnd_1718453 < baseStart_1718453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718493 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1718493 : Nat := 118140960795 + 1718493 * 2 ^ 59
def prefixEnd_1718493 : Nat := 4983230072969 + 3 ^ 40 * 1718493 * 2
def baseEnd_1718493 : Nat := 882412910387050121934301

theorem tailTrace_1718493 : CollatzResearch.WordTrace tailWord_1718493 prefixEnd_1718493 882412910387050121934301 := by
  unfold tailWord_1718493
  simp only [CollatzResearch.WordTrace]
  refine ⟨62678588963200831083160133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41785725975467220722106755 62678588963200831083160133)
  ·
    refine ⟨11752235430600155828092525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62678588963200831083160133 11752235430600155828092525)
    ·
      refine ⟨4407088286475058435534697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11752235430600155828092525 4407088286475058435534697)
      ·
        refine ⟨3305316214856293826651023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4407088286475058435534697 3305316214856293826651023)
        ·
          refine ⟨4957974322284440739976535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305316214856293826651023 4957974322284440739976535)
          ·
            refine ⟨7436961483426661109964803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957974322284440739976535 7436961483426661109964803)
            ·
              refine ⟨11155442225139991664947205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436961483426661109964803 11155442225139991664947205)
              ·
                refine ⟨2091645417213748437177601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11155442225139991664947205 2091645417213748437177601)
                ·
                  refine ⟨1568734062910311327883201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2091645417213748437177601 1568734062910311327883201)
                  ·
                    refine ⟨1176550547182733495912401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1568734062910311327883201 1176550547182733495912401)
                    ·
                      refine ⟨882412910387050121934301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176550547182733495912401 882412910387050121934301)
                      ·
                        rfl

theorem cell23_1718493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1718493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718493 prefixEnd_1718493 := by exact prefixLift 1718493
  have htrace : WordTrace (prefixWord ++ tailWord_1718493) baseStart_1718493 baseEnd_1718493 := by
    simpa [prefixWord, tailWord_1718493, baseEnd_1718493] using wordTrace_append hprefix tailTrace_1718493
  have hstable : (prefixWord ++ tailWord_1718493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718493).length < 2 ^ (prefixWord ++ tailWord_1718493).sum := by decide
  have hdescent : baseEnd_1718493 < baseStart_1718493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718495 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 7]
def baseStart_1718495 : Nat := 118140960795 + 1718495 * 2 ^ 59
def prefixEnd_1718495 : Nat := 4983230072969 + 3 ^ 40 * 1718495 * 2
def baseEnd_1718495 : Nat := 294137979116119704703097

theorem tailTrace_1718495 : CollatzResearch.WordTrace tailWord_1718495 prefixEnd_1718495 294137979116119704703097 := by
  unfold tailWord_1718495
  simp only [CollatzResearch.WordTrace]
  refine ⟨62678661909193585424732939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41785774606129056949821959 62678661909193585424732939)
  ·
    refine ⟨94017992863790378137099409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62678661909193585424732939 94017992863790378137099409)
    ·
      refine ⟨70513494647842783602824557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94017992863790378137099409 70513494647842783602824557)
      ·
        refine ⟨26442560492941043851059209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70513494647842783602824557 26442560492941043851059209)
        ·
          refine ⟨19831920369705782888294407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26442560492941043851059209 19831920369705782888294407)
          ·
            refine ⟨29747880554558674332441611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19831920369705782888294407 29747880554558674332441611)
            ·
              refine ⟨44621820831838011498662417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29747880554558674332441611 44621820831838011498662417)
              ·
                refine ⟨33466365623878508623996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44621820831838011498662417 33466365623878508623996813)
                ·
                  refine ⟨12549887108954440733998805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33466365623878508623996813 12549887108954440733998805)
                  ·
                    refine ⟨294137979116119704703097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12549887108954440733998805 294137979116119704703097)
                    ·
                      rfl

theorem cell23_1718495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_1718495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718495 prefixEnd_1718495 := by exact prefixLift 1718495
  have htrace : WordTrace (prefixWord ++ tailWord_1718495) baseStart_1718495 baseEnd_1718495 := by
    simpa [prefixWord, tailWord_1718495, baseEnd_1718495] using wordTrace_append hprefix tailTrace_1718495
  have hstable : (prefixWord ++ tailWord_1718495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718495).length < 2 ^ (prefixWord ++ tailWord_1718495).sum := by decide
  have hdescent : baseEnd_1718495 < baseStart_1718495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718549 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_1718549 : Nat := 118140960795 + 1718549 * 2 ^ 59
def prefixEnd_1718549 : Nat := 4983230072969 + 3 ^ 40 * 1718549 * 2
def baseEnd_1718549 : Nat := 882441665303701902834043

theorem tailTrace_1718549 : CollatzResearch.WordTrace tailWord_1718549 prefixEnd_1718549 882441665303701902834043 := by
  unfold tailWord_1718549
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680631450997952647198701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41787087633998635098132467 62680631450997952647198701)
  ·
    refine ⟨23505236794124232242699513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62680631450997952647198701 23505236794124232242699513)
    ·
      refine ⟨17628927595593174182024635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23505236794124232242699513 17628927595593174182024635)
      ·
        refine ⟨26443391393389761273036953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17628927595593174182024635 26443391393389761273036953)
        ·
          refine ⟨19832543545042320954777715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26443391393389761273036953 19832543545042320954777715)
          ·
            refine ⟨29748815317563481432166573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19832543545042320954777715 29748815317563481432166573)
            ·
              refine ⟨11155805744086305537062465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29748815317563481432166573 11155805744086305537062465)
              ·
                refine ⟨8366854308064729152796849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11155805744086305537062465 8366854308064729152796849)
                ·
                  refine ⟨6275140731048546864597637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8366854308064729152796849 6275140731048546864597637)
                  ·
                    refine ⟨1176588887071602537112057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6275140731048546864597637 1176588887071602537112057)
                    ·
                      refine ⟨882441665303701902834043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176588887071602537112057 882441665303701902834043)
                      ·
                        rfl

theorem cell23_1718549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_1718549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718549 prefixEnd_1718549 := by exact prefixLift 1718549
  have htrace : WordTrace (prefixWord ++ tailWord_1718549) baseStart_1718549 baseEnd_1718549 := by
    simpa [prefixWord, tailWord_1718549, baseEnd_1718549] using wordTrace_append hprefix tailTrace_1718549
  have hstable : (prefixWord ++ tailWord_1718549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718549).length < 2 ^ (prefixWord ++ tailWord_1718549).sum := by decide
  have hdescent : baseEnd_1718549 < baseStart_1718549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718559 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 3, 4]
def baseStart_1718559 : Nat := 118140960795 + 1718559 * 2 ^ 59
def prefixEnd_1718559 : Nat := 4983230072969 + 3 ^ 40 * 1718559 * 2
def baseEnd_1718559 : Nat := 294148933370082287902999

theorem tailTrace_1718559 : CollatzResearch.WordTrace tailWord_1718559 prefixEnd_1718559 294148933370082287902999 := by
  unfold tailWord_1718559
  simp only [CollatzResearch.WordTrace]
  refine ⟨62680996180961724355062731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41787330787307816236708487 62680996180961724355062731)
  ·
    refine ⟨94021494271442586532594097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62680996180961724355062731 94021494271442586532594097)
    ·
      refine ⟨70516120703581939899445573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94021494271442586532594097 70516120703581939899445573)
      ·
        refine ⟨13221772631921613731146045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70516120703581939899445573 13221772631921613731146045)
        ·
          refine ⟨4958164736970605149179767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13221772631921613731146045 4958164736970605149179767)
          ·
            refine ⟨7437247105455907723769651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958164736970605149179767 7437247105455907723769651)
            ·
              refine ⟨11155870658183861585654477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437247105455907723769651 11155870658183861585654477)
              ·
                refine ⟨4183451496818948094620429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11155870658183861585654477 4183451496818948094620429)
                ·
                  refine ⟨1568794311307105535482661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4183451496818948094620429 1568794311307105535482661)
                  ·
                    refine ⟨294148933370082287902999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1568794311307105535482661 294148933370082287902999)
                    ·
                      rfl

theorem cell23_1718559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_1718559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718559 prefixEnd_1718559 := by exact prefixLift 1718559
  have htrace : WordTrace (prefixWord ++ tailWord_1718559) baseStart_1718559 baseEnd_1718559 := by
    simpa [prefixWord, tailWord_1718559, baseEnd_1718559] using wordTrace_append hprefix tailTrace_1718559
  have hstable : (prefixWord ++ tailWord_1718559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718559).length < 2 ^ (prefixWord ++ tailWord_1718559).sum := by decide
  have hdescent : baseEnd_1718559 < baseStart_1718559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718572 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 6]
def baseStart_1718572 : Nat := 118140960795 + 1718572 * 2 ^ 59
def prefixEnd_1718572 : Nat := 4983230072969 + 3 ^ 40 * 1718572 * 2
def baseEnd_1718572 : Nat := 98050386150972812538493

theorem tailTrace_1718572 : CollatzResearch.WordTrace tailWord_1718572 prefixEnd_1718572 98050386150972812538493 := by
  unfold tailWord_1718572
  simp only [CollatzResearch.WordTrace]
  refine ⟨31340735164957313787642985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41787646886609751716857313 31340735164957313787642985)
  ·
    refine ⟨23505551373717985340732239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31340735164957313787642985 23505551373717985340732239)
    ·
      refine ⟨35258327060576978011098359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23505551373717985340732239 35258327060576978011098359)
      ·
        refine ⟨52887490590865467016647539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35258327060576978011098359 52887490590865467016647539)
        ·
          refine ⟨79331235886298200524971309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52887490590865467016647539 79331235886298200524971309)
          ·
            refine ⟨29749213457361825196864241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79331235886298200524971309 29749213457361825196864241)
            ·
              refine ⟨22311910093021368897648181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29749213457361825196864241 22311910093021368897648181)
              ·
                refine ⟨2091741571220753334154517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22311910093021368897648181 2091741571220753334154517)
                ·
                  refine ⟨98050386150972812538493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2091741571220753334154517 98050386150972812538493)
                  ·
                    rfl

theorem cell23_1718572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_1718572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718572 prefixEnd_1718572 := by exact prefixLift 1718572
  have htrace : WordTrace (prefixWord ++ tailWord_1718572) baseStart_1718572 baseEnd_1718572 := by
    simpa [prefixWord, tailWord_1718572, baseEnd_1718572] using wordTrace_append hprefix tailTrace_1718572
  have hstable : (prefixWord ++ tailWord_1718572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718572).length < 2 ^ (prefixWord ++ tailWord_1718572).sum := by decide
  have hdescent : baseEnd_1718572 < baseStart_1718572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718602 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1718602 : Nat := 118140960795 + 1718602 * 2 ^ 59
def prefixEnd_1718602 : Nat := 4983230072969 + 3 ^ 40 * 1718602 * 2
def baseEnd_1718602 : Nat := 294156293259463398490433

theorem tailTrace_1718602 : CollatzResearch.WordTrace tailWord_1718602 prefixEnd_1718602 294156293259463398490433 := by
  unfold tailWord_1718602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15670641129951485674719515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41788376346537295132585373 15670641129951485674719515)
  ·
    refine ⟨23505961694927228512079273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15670641129951485674719515 23505961694927228512079273)
    ·
      refine ⟨17629471271195421384059455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23505961694927228512079273 17629471271195421384059455)
      ·
        refine ⟨26444206906793132076089183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17629471271195421384059455 26444206906793132076089183)
        ·
          refine ⟨39666310360189698114133775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26444206906793132076089183 39666310360189698114133775)
          ·
            refine ⟨59499465540284547171200663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39666310360189698114133775 59499465540284547171200663)
            ·
              refine ⟨89249198310426820756800995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59499465540284547171200663 89249198310426820756800995)
              ·
                refine ⟨133873797465640231135201493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89249198310426820756800995 133873797465640231135201493)
                ·
                  refine ⟨3137667128100942917231285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133873797465640231135201493 3137667128100942917231285)
                  ·
                    refine ⟨294156293259463398490433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3137667128100942917231285 294156293259463398490433)
                    ·
                      rfl

theorem cell23_1718602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1718602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718602 prefixEnd_1718602 := by exact prefixLift 1718602
  have htrace : WordTrace (prefixWord ++ tailWord_1718602) baseStart_1718602 baseEnd_1718602 := by
    simpa [prefixWord, tailWord_1718602, baseEnd_1718602] using wordTrace_append hprefix tailTrace_1718602
  have hstable : (prefixWord ++ tailWord_1718602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718602).length < 2 ^ (prefixWord ++ tailWord_1718602).sum := by decide
  have hdescent : baseEnd_1718602 < baseStart_1718602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718639 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_1718639 : Nat := 118140960795 + 1718639 * 2 ^ 59
def prefixEnd_1718639 : Nat := 4983230072969 + 3 ^ 40 * 1718639 * 2
def baseEnd_1718639 : Nat := 882487878562606550708629

theorem tailTrace_1718639 : CollatzResearch.WordTrace tailWord_1718639 prefixEnd_1718639 882487878562606550708629 := by
  unfold tailWord_1718639
  simp only [CollatzResearch.WordTrace]
  refine ⟨62683914020671898017974971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41789276013781265345316647 62683914020671898017974971)
  ·
    refine ⟨94025871031007847026962457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62683914020671898017974971 94025871031007847026962457)
    ·
      refine ⟨70519403273255885270221843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94025871031007847026962457 70519403273255885270221843)
      ·
        refine ⟨105779104909883827905332765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70519403273255885270221843 105779104909883827905332765)
        ·
          refine ⟨39667164341206435464499787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105779104909883827905332765 39667164341206435464499787)
          ·
            refine ⟨59500746511809653196749681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39667164341206435464499787 59500746511809653196749681)
            ·
              refine ⟨44625559883857239897562261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59500746511809653196749681 44625559883857239897562261)
              ·
                refine ⟨2091823119555808120198231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44625559883857239897562261 2091823119555808120198231)
                ·
                  refine ⟨3137734679333712180297347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091823119555808120198231 3137734679333712180297347)
                  ·
                    refine ⟨4706602019000568270446021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3137734679333712180297347 4706602019000568270446021)
                    ·
                      refine ⟨882487878562606550708629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4706602019000568270446021 882487878562606550708629)
                      ·
                        rfl

theorem cell23_1718639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_1718639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718639 prefixEnd_1718639 := by exact prefixLift 1718639
  have htrace : WordTrace (prefixWord ++ tailWord_1718639) baseStart_1718639 baseEnd_1718639 := by
    simpa [prefixWord, tailWord_1718639, baseEnd_1718639] using wordTrace_append hprefix tailTrace_1718639
  have hstable : (prefixWord ++ tailWord_1718639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718639).length < 2 ^ (prefixWord ++ tailWord_1718639).sum := by decide
  have hdescent : baseEnd_1718639 < baseStart_1718639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718652 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1718652 : Nat := 118140960795 + 1718652 * 2 ^ 59
def prefixEnd_1718652 : Nat := 4983230072969 + 3 ^ 40 * 1718652 * 2
def baseEnd_1718652 : Nat := 882494553811114999846069

theorem tailTrace_1718652 : CollatzResearch.WordTrace tailWord_1718652 prefixEnd_1718652 882494553811114999846069 := by
  unfold tailWord_1718652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31342194084812400619099105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41789592113083200825465473 31342194084812400619099105)
  ·
    refine ⟨23506645563609300464324329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31342194084812400619099105 23506645563609300464324329)
    ·
      refine ⟨17629984172706975348243247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23506645563609300464324329 17629984172706975348243247)
      ·
        refine ⟨26444976259060463022364871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17629984172706975348243247 26444976259060463022364871)
        ·
          refine ⟨39667464388590694533547307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26444976259060463022364871 39667464388590694533547307)
          ·
            refine ⟨59501196582886041800320961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39667464388590694533547307 59501196582886041800320961)
            ·
              refine ⟨44625897437164531350240721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59501196582886041800320961 44625897437164531350240721)
              ·
                refine ⟨33469423077873398512680541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44625897437164531350240721 33469423077873398512680541)
                ·
                  refine ⟨12551033654202524442255203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33469423077873398512680541 12551033654202524442255203)
                  ·
                    refine ⟨18826550481303786663382805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12551033654202524442255203 18826550481303786663382805)
                    ·
                      refine ⟨882494553811114999846069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18826550481303786663382805 882494553811114999846069)
                      ·
                        rfl

theorem cell23_1718652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1718652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718652 prefixEnd_1718652 := by exact prefixLift 1718652
  have htrace : WordTrace (prefixWord ++ tailWord_1718652) baseStart_1718652 baseEnd_1718652 := by
    simpa [prefixWord, tailWord_1718652, baseEnd_1718652] using wordTrace_append hprefix tailTrace_1718652
  have hstable : (prefixWord ++ tailWord_1718652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718652).length < 2 ^ (prefixWord ++ tailWord_1718652).sum := by decide
  have hdescent : baseEnd_1718652 < baseStart_1718652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718706 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1718706 : Nat := 118140960795 + 1718706 * 2 ^ 59
def prefixEnd_1718706 : Nat := 4983230072969 + 3 ^ 40 * 1718706 * 2
def baseEnd_1718706 : Nat := 882522281766457788570821

theorem tailTrace_1718706 : CollatzResearch.WordTrace tailWord_1718706 prefixEnd_1718706 882522281766457788570821 := by
  unfold tailWord_1718706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671589427857292115165993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41790905140952778973775981 15671589427857292115165993)
  ·
    refine ⟨11753692070892969086374495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15671589427857292115165993 11753692070892969086374495)
    ·
      refine ⟨17630538106339453629561743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11753692070892969086374495 17630538106339453629561743)
      ·
        refine ⟨26445807159509180444342615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17630538106339453629561743 26445807159509180444342615)
        ·
          refine ⟨39668710739263770666513923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26445807159509180444342615 39668710739263770666513923)
          ·
            refine ⟨59503066108895655999770885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39668710739263770666513923 59503066108895655999770885)
            ·
              refine ⟨11156824895417935499957041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59503066108895655999770885 11156824895417935499957041)
              ·
                refine ⟨8367618671563451624967781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11156824895417935499957041 8367618671563451624967781)
                ·
                  refine ⟨1568928500918147179681459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8367618671563451624967781 1568928500918147179681459)
                  ·
                    refine ⟨2353392751377220769522189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1568928500918147179681459 2353392751377220769522189)
                    ·
                      refine ⟨882522281766457788570821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2353392751377220769522189 882522281766457788570821)
                      ·
                        rfl

theorem cell23_1718706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1718706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718706 prefixEnd_1718706 := by exact prefixLift 1718706
  have htrace : WordTrace (prefixWord ++ tailWord_1718706) baseStart_1718706 baseEnd_1718706 := by
    simpa [prefixWord, tailWord_1718706, baseEnd_1718706] using wordTrace_append hprefix tailTrace_1718706
  have hstable : (prefixWord ++ tailWord_1718706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718706).length < 2 ^ (prefixWord ++ tailWord_1718706).sum := by decide
  have hdescent : baseEnd_1718706 < baseStart_1718706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718766 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1718766 : Nat := 118140960795 + 1718766 * 2 ^ 59
def prefixEnd_1718766 : Nat := 4983230072969 + 3 ^ 40 * 1718766 * 2
def baseEnd_1718766 : Nat := 882553090605727553820545

theorem tailTrace_1718766 : CollatzResearch.WordTrace tailWord_1718766 prefixEnd_1718766 882553090605727553820545 := by
  unfold tailWord_1718766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836068261401474838481019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41792364060807865805232101 7836068261401474838481019)
  ·
    refine ⟨11754102392102212257721529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7836068261401474838481019 11754102392102212257721529)
    ·
      refine ⟨8815576794076659193291147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11754102392102212257721529 8815576794076659193291147)
      ·
        refine ⟨13223365191114988789936721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8815576794076659193291147 13223365191114988789936721)
        ·
          refine ⟨9917523893336241592452541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13223365191114988789936721 9917523893336241592452541)
          ·
            refine ⟨3719071460001090597169703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9917523893336241592452541 3719071460001090597169703)
            ·
              refine ⟨5578607190001635895754555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719071460001090597169703 5578607190001635895754555)
              ·
                refine ⟨8367910785002453843631833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578607190001635895754555 8367910785002453843631833)
                ·
                  refine ⟨6275933088751840382723875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367910785002453843631833 6275933088751840382723875)
                  ·
                    refine ⟨9413899633127760574085813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6275933088751840382723875 9413899633127760574085813)
                    ·
                      refine ⟨882553090605727553820545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9413899633127760574085813 882553090605727553820545)
                      ·
                        rfl

theorem cell23_1718766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1718766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718766 prefixEnd_1718766 := by exact prefixLift 1718766
  have htrace : WordTrace (prefixWord ++ tailWord_1718766) baseStart_1718766 baseEnd_1718766 := by
    simpa [prefixWord, tailWord_1718766, baseEnd_1718766] using wordTrace_append hprefix tailTrace_1718766
  have hstable : (prefixWord ++ tailWord_1718766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718766).length < 2 ^ (prefixWord ++ tailWord_1718766).sum := by decide
  have hdescent : baseEnd_1718766 < baseStart_1718766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718826 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1718826 : Nat := 118140960795 + 1718826 * 2 ^ 59
def prefixEnd_1718826 : Nat := 4983230072969 + 3 ^ 40 * 1718826 * 2
def baseEnd_1718826 : Nat := 882583899444997319070269

theorem tailTrace_1718826 : CollatzResearch.WordTrace tailWord_1718826 prefixEnd_1718826 882583899444997319070269 := by
  unfold tailWord_1718826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672683617748607238758083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41793822980662952636688221 15672683617748607238758083)
  ·
    refine ⟨23509025426622910858137125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15672683617748607238758083 23509025426622910858137125)
    ·
      refine ⟨4407942267491795785900711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23509025426622910858137125 4407942267491795785900711)
      ·
        refine ⟨6611913401237693678851067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407942267491795785900711 6611913401237693678851067)
        ·
          refine ⟨9917870101856540518276601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611913401237693678851067 9917870101856540518276601)
          ·
            refine ⟨7438402576392405388707451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917870101856540518276601 7438402576392405388707451)
            ·
              refine ⟨11157603864588608083061177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438402576392405388707451 11157603864588608083061177)
              ·
                refine ⟨8368202898441456062295883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157603864588608083061177 8368202898441456062295883)
                ·
                  refine ⟨12552304347662184093443825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8368202898441456062295883 12552304347662184093443825)
                  ·
                    refine ⟨9414228260746638070082869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12552304347662184093443825 9414228260746638070082869)
                    ·
                      refine ⟨882583899444997319070269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9414228260746638070082869 882583899444997319070269)
                      ·
                        rfl

theorem cell23_1718826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1718826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718826 prefixEnd_1718826 := by exact prefixLift 1718826
  have htrace : WordTrace (prefixWord ++ tailWord_1718826) baseStart_1718826 baseEnd_1718826 := by
    simpa [prefixWord, tailWord_1718826, baseEnd_1718826] using wordTrace_append hprefix tailTrace_1718826
  have hstable : (prefixWord ++ tailWord_1718826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718826).length < 2 ^ (prefixWord ++ tailWord_1718826).sum := by decide
  have hdescent : baseEnd_1718826 < baseStart_1718826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718839 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1718839 : Nat := 118140960795 + 1718839 * 2 ^ 59
def prefixEnd_1718839 : Nat := 4983230072969 + 3 ^ 40 * 1718839 * 2
def baseEnd_1718839 : Nat := 882590574693505768207709

theorem tailTrace_1718839 : CollatzResearch.WordTrace tailWord_1718839 prefixEnd_1718839 882590574693505768207709 := by
  unfold tailWord_1718839
  simp only [CollatzResearch.WordTrace]
  refine ⟨62691208619947332175255571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41794139079964888116837047 62691208619947332175255571)
  ·
    refine ⟨94036812929920998262883357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62691208619947332175255571 94036812929920998262883357)
    ·
      refine ⟨35263804848720374348581259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94036812929920998262883357 35263804848720374348581259)
      ·
        refine ⟨52895707273080561522871889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35263804848720374348581259 52895707273080561522871889)
        ·
          refine ⟨39671780454810421142153917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52895707273080561522871889 39671780454810421142153917)
          ·
            refine ⟨14876917670553907928307719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39671780454810421142153917 14876917670553907928307719)
            ·
              refine ⟨22315376505830861892461579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876917670553907928307719 22315376505830861892461579)
              ·
                refine ⟨33473064758746292838692369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22315376505830861892461579 33473064758746292838692369)
                ·
                  refine ⟨25104798569059719629019277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33473064758746292838692369 25104798569059719629019277)
                  ·
                    refine ⟨9414299463397394860882229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25104798569059719629019277 9414299463397394860882229)
                    ·
                      refine ⟨882590574693505768207709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9414299463397394860882229 882590574693505768207709)
                      ·
                        rfl

theorem cell23_1718839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1718839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718839 prefixEnd_1718839 := by exact prefixLift 1718839
  have htrace : WordTrace (prefixWord ++ tailWord_1718839) baseStart_1718839 baseEnd_1718839 := by
    simpa [prefixWord, tailWord_1718839, baseEnd_1718839] using wordTrace_append hprefix tailTrace_1718839
  have hstable : (prefixWord ++ tailWord_1718839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718839).length < 2 ^ (prefixWord ++ tailWord_1718839).sum := by decide
  have hdescent : baseEnd_1718839 < baseStart_1718839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718853 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_1718853 : Nat := 118140960795 + 1718853 * 2 ^ 59
def prefixEnd_1718853 : Nat := 4983230072969 + 3 ^ 40 * 1718853 * 2
def baseEnd_1718853 : Nat := 882597763422668713432645

theorem tailTrace_1718853 : CollatzResearch.WordTrace tailWord_1718853 prefixEnd_1718853 882597763422668713432645 := by
  unfold tailWord_1718853
  simp only [CollatzResearch.WordTrace]
  refine ⟨62691719241896612566265213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41794479494597741710843475 62691719241896612566265213)
  ·
    refine ⟨23509394715711229712349455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62691719241896612566265213 23509394715711229712349455)
    ·
      refine ⟨35264092073566844568524183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23509394715711229712349455 35264092073566844568524183)
      ·
        refine ⟨52896138110350266852786275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35264092073566844568524183 52896138110350266852786275)
        ·
          refine ⟨79344207165525400279179413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52896138110350266852786275 79344207165525400279179413)
          ·
            refine ⟨3719259710884003138086535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79344207165525400279179413 3719259710884003138086535)
            ·
              refine ⟨5578889566326004707129803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719259710884003138086535 5578889566326004707129803)
              ·
                refine ⟨8368334349489007060694705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578889566326004707129803 8368334349489007060694705)
                ·
                  refine ⟨6276250762116755295521029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8368334349489007060694705 6276250762116755295521029)
                  ·
                    refine ⟨1176797017896891617910193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276250762116755295521029 1176797017896891617910193)
                    ·
                      refine ⟨882597763422668713432645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176797017896891617910193 882597763422668713432645)
                      ·
                        rfl

theorem cell23_1718853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_1718853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718853 prefixEnd_1718853 := by exact prefixLift 1718853
  have htrace : WordTrace (prefixWord ++ tailWord_1718853) baseStart_1718853 baseEnd_1718853 := by
    simpa [prefixWord, tailWord_1718853, baseEnd_1718853] using wordTrace_append hprefix tailTrace_1718853
  have hstable : (prefixWord ++ tailWord_1718853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718853).length < 2 ^ (prefixWord ++ tailWord_1718853).sum := by decide
  have hdescent : baseEnd_1718853 < baseStart_1718853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718856 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1718856 : Nat := 118140960795 + 1718856 * 2 ^ 59
def prefixEnd_1718856 : Nat := 4983230072969 + 3 ^ 40 * 1718856 * 2
def baseEnd_1718856 : Nat := 882599303864632201695131

theorem tailTrace_1718856 : CollatzResearch.WordTrace tailWord_1718856 prefixEnd_1718856 882599303864632201695131 := by
  unfold tailWord_1718856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31345914330442872039312211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41794552440590496052416281 31345914330442872039312211)
  ·
    refine ⟨47018871495664308058968317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31345914330442872039312211 47018871495664308058968317)
    ·
      refine ⟨17632076810874115522113119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47018871495664308058968317 17632076810874115522113119)
      ·
        refine ⟨26448115216311173283169679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17632076810874115522113119 26448115216311173283169679)
        ·
          refine ⟨39672172824466759924754519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26448115216311173283169679 39672172824466759924754519)
          ·
            refine ⟨59508259236700139887131779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39672172824466759924754519 59508259236700139887131779)
            ·
              refine ⟨89262388855050209830697669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59508259236700139887131779 89262388855050209830697669)
              ·
                refine ⟨16736697910321914343255813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89262388855050209830697669 16736697910321914343255813)
                ·
                  refine ⟨3138130858185358939360465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16736697910321914343255813 3138130858185358939360465)
                  ·
                    refine ⟨2353598143639019204520349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138130858185358939360465 2353598143639019204520349)
                    ·
                      refine ⟨882599303864632201695131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2353598143639019204520349 882599303864632201695131)
                      ·
                        rfl

theorem cell23_1718856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1718856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718856 prefixEnd_1718856 := by exact prefixLift 1718856
  have htrace : WordTrace (prefixWord ++ tailWord_1718856) baseStart_1718856 baseEnd_1718856 := by
    simpa [prefixWord, tailWord_1718856, baseEnd_1718856] using wordTrace_append hprefix tailTrace_1718856
  have hstable : (prefixWord ++ tailWord_1718856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718856).length < 2 ^ (prefixWord ++ tailWord_1718856).sum := by decide
  have hdescent : baseEnd_1718856 < baseStart_1718856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718879 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1718879 : Nat := 118140960795 + 1718879 * 2 ^ 59
def prefixEnd_1718879 : Nat := 4983230072969 + 3 ^ 40 * 1718879 * 2
def baseEnd_1718879 : Nat := 882611113919685611707525

theorem tailTrace_1718879 : CollatzResearch.WordTrace tailWord_1718879 prefixEnd_1718879 882611113919685611707525 := by
  unfold tailWord_1718879
  simp only [CollatzResearch.WordTrace]
  refine ⟨62692667539802419006711691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41795111693201612671141127 62692667539802419006711691)
  ·
    refine ⟨94039001309703628510067537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62692667539802419006711691 94039001309703628510067537)
    ·
      refine ⟨70529250982277721382550653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94039001309703628510067537 70529250982277721382550653)
      ·
        refine ⟨26448469118354145518456495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70529250982277721382550653 26448469118354145518456495)
        ·
          refine ⟨39672703677531218277684743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26448469118354145518456495 39672703677531218277684743)
          ·
            refine ⟨59509055516296827416527115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39672703677531218277684743 59509055516296827416527115)
            ·
              refine ⟨89263583274445241124790673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59509055516296827416527115 89263583274445241124790673)
              ·
                refine ⟨66947687455833930843593005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89263583274445241124790673 66947687455833930843593005)
                ·
                  refine ⟨25105382795937724066347377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66947687455833930843593005 25105382795937724066347377)
                  ·
                    refine ⟨18829037096953293049760533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25105382795937724066347377 18829037096953293049760533)
                    ·
                      refine ⟨882611113919685611707525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18829037096953293049760533 882611113919685611707525)
                      ·
                        rfl

theorem cell23_1718879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1718879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718879 prefixEnd_1718879 := by exact prefixLift 1718879
  have htrace : WordTrace (prefixWord ++ tailWord_1718879) baseStart_1718879 baseEnd_1718879 := by
    simpa [prefixWord, tailWord_1718879, baseEnd_1718879] using wordTrace_append hprefix tailTrace_1718879
  have hstable : (prefixWord ++ tailWord_1718879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718879).length < 2 ^ (prefixWord ++ tailWord_1718879).sum := by decide
  have hdescent : baseEnd_1718879 < baseStart_1718879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718893 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 6]
def baseStart_1718893 : Nat := 118140960795 + 1718893 * 2 ^ 59
def prefixEnd_1718893 : Nat := 4983230072969 + 3 ^ 40 * 1718893 * 2
def baseEnd_1718893 : Nat := 98068700294316506325829

theorem tailTrace_1718893 : CollatzResearch.WordTrace tailWord_1718893 prefixEnd_1718893 98068700294316506325829 := by
  unfold tailWord_1718893
  simp only [CollatzResearch.WordTrace]
  refine ⟨62693178161751699397721333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41795452107834466265147555 62693178161751699397721333)
  ·
    refine ⟨5877485452664221818536375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62693178161751699397721333 5877485452664221818536375)
    ·
      refine ⟨8816228178996332727804563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877485452664221818536375 8816228178996332727804563)
      ·
        refine ⟨13224342268494499091706845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816228178996332727804563 13224342268494499091706845)
        ·
          refine ⟨4959128350685437159390067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13224342268494499091706845 4959128350685437159390067)
          ·
            refine ⟨7438692526028155739085101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959128350685437159390067 7438692526028155739085101)
            ·
              refine ⟨2789509697260558402156913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7438692526028155739085101 2789509697260558402156913)
              ·
                refine ⟨2092132272945418801617685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789509697260558402156913 2092132272945418801617685)
                ·
                  refine ⟨98068700294316506325829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2092132272945418801617685 98068700294316506325829)
                  ·
                    rfl

theorem cell23_1718893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_1718893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718893 prefixEnd_1718893 := by exact prefixLift 1718893
  have htrace : WordTrace (prefixWord ++ tailWord_1718893) baseStart_1718893 baseEnd_1718893 := by
    simpa [prefixWord, tailWord_1718893, baseEnd_1718893] using wordTrace_append hprefix tailTrace_1718893
  have hstable : (prefixWord ++ tailWord_1718893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718893).length < 2 ^ (prefixWord ++ tailWord_1718893).sum := by decide
  have hdescent : baseEnd_1718893 < baseStart_1718893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718899 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_1718899 : Nat := 118140960795 + 1718899 * 2 ^ 59
def prefixEnd_1718899 : Nat := 4983230072969 + 3 ^ 40 * 1718899 * 2
def baseEnd_1718899 : Nat := 882621383532775533457433

theorem tailTrace_1718899 : CollatzResearch.WordTrace tailWord_1718899 prefixEnd_1718899 882621383532775533457433 := by
  unfold tailWord_1718899
  simp only [CollatzResearch.WordTrace]
  refine ⟨62693396999729962422439751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41795597999819974948293167 62693396999729962422439751)
  ·
    refine ⟨94040095499594943633659627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62693396999729962422439751 94040095499594943633659627)
    ·
      refine ⟨141060143249392415450489441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94040095499594943633659627 141060143249392415450489441)
      ·
        refine ⟨105795107437044311587867081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141060143249392415450489441 105795107437044311587867081)
        ·
          refine ⟨79346330577783233690900311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105795107437044311587867081 79346330577783233690900311)
          ·
            refine ⟨119019495866674850536350467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79346330577783233690900311 119019495866674850536350467)
            ·
              refine ⟨178529243800012275804525701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119019495866674850536350467 178529243800012275804525701)
              ·
                refine ⟨33474233212502301713348569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178529243800012275804525701 33474233212502301713348569)
                ·
                  refine ⟨25105674909376726285011427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33474233212502301713348569 25105674909376726285011427)
                  ·
                    refine ⟨37658512364065089427517141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25105674909376726285011427 37658512364065089427517141)
                    ·
                      refine ⟨882621383532775533457433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37658512364065089427517141 882621383532775533457433)
                      ·
                        rfl

theorem cell23_1718899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_1718899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718899 prefixEnd_1718899 := by exact prefixLift 1718899
  have htrace : WordTrace (prefixWord ++ tailWord_1718899) baseStart_1718899 baseEnd_1718899 := by
    simpa [prefixWord, tailWord_1718899, baseEnd_1718899] using wordTrace_append hprefix tailTrace_1718899
  have hstable : (prefixWord ++ tailWord_1718899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718899).length < 2 ^ (prefixWord ++ tailWord_1718899).sum := by decide
  have hdescent : baseEnd_1718899 < baseStart_1718899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718903 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_1718903 : Nat := 118140960795 + 1718903 * 2 ^ 59
def prefixEnd_1718903 : Nat := 4983230072969 + 3 ^ 40 * 1718903 * 2
def baseEnd_1718903 : Nat := 882623437455393517807415

theorem tailTrace_1718903 : CollatzResearch.WordTrace tailWord_1718903 prefixEnd_1718903 882623437455393517807415 := by
  unfold tailWord_1718903
  simp only [CollatzResearch.WordTrace]
  refine ⟨62693542891715471105585363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41795695261143647403723575 62693542891715471105585363)
  ·
    refine ⟨94040314337573206658378045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62693542891715471105585363 94040314337573206658378045)
    ·
      refine ⟨35265117876589952496891767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94040314337573206658378045 35265117876589952496891767)
      ·
        refine ⟨52897676814884928745337651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35265117876589952496891767 52897676814884928745337651)
        ·
          refine ⟨79346515222327393118006477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52897676814884928745337651 79346515222327393118006477)
          ·
            refine ⟨29754943208372772419252429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79346515222327393118006477 29754943208372772419252429)
            ·
              refine ⟨11158103703139789657219661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29754943208372772419252429 11158103703139789657219661)
              ·
                refine ⟨4184288888677421121457373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11158103703139789657219661 4184288888677421121457373)
                ·
                  refine ⟨1569108333254032920546515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4184288888677421121457373 1569108333254032920546515)
                  ·
                    refine ⟨2353662499881049380819773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1569108333254032920546515 2353662499881049380819773)
                    ·
                      refine ⟨882623437455393517807415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2353662499881049380819773 882623437455393517807415)
                      ·
                        rfl

theorem cell23_1718903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_1718903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718903 prefixEnd_1718903 := by exact prefixLift 1718903
  have htrace : WordTrace (prefixWord ++ tailWord_1718903) baseStart_1718903 baseEnd_1718903 := by
    simpa [prefixWord, tailWord_1718903, baseEnd_1718903] using wordTrace_append hprefix tailTrace_1718903
  have hstable : (prefixWord ++ tailWord_1718903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718903).length < 2 ^ (prefixWord ++ tailWord_1718903).sum := by decide
  have hdescent : baseEnd_1718903 < baseStart_1718903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718913 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1718913 : Nat := 118140960795 + 1718913 * 2 ^ 59
def prefixEnd_1718913 : Nat := 4983230072969 + 3 ^ 40 * 1718913 * 2
def baseEnd_1718913 : Nat := 882628572261938478682369

theorem tailTrace_1718913 : CollatzResearch.WordTrace tailWord_1718913 prefixEnd_1718913 882628572261938478682369 := by
  unfold tailWord_1718913
  simp only [CollatzResearch.WordTrace]
  refine ⟨62693907621679242813449393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41795938414452828542299595 62693907621679242813449393)
  ·
    refine ⟨47020430716259432110087045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62693907621679242813449393 47020430716259432110087045)
    ·
      refine ⟨8816330759298643520641321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47020430716259432110087045 8816330759298643520641321)
      ·
        refine ⟨6612248069473982640480991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816330759298643520641321 6612248069473982640480991)
        ·
          refine ⟨9918372104210973960721487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612248069473982640480991 9918372104210973960721487)
          ·
            refine ⟨14877558156316460941082231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918372104210973960721487 14877558156316460941082231)
            ·
              refine ⟨22316337234474691411623347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877558156316460941082231 22316337234474691411623347)
              ·
                refine ⟨33474505851712037117435021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22316337234474691411623347 33474505851712037117435021)
                ·
                  refine ⟨12552939694392013919038133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33474505851712037117435021 12552939694392013919038133)
                  ·
                    refine ⟨1176838096349251304909825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12552939694392013919038133 1176838096349251304909825)
                    ·
                      refine ⟨882628572261938478682369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176838096349251304909825 882628572261938478682369)
                      ·
                        rfl

theorem cell23_1718913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1718913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718913 prefixEnd_1718913 := by exact prefixLift 1718913
  have htrace : WordTrace (prefixWord ++ tailWord_1718913) baseStart_1718913 baseEnd_1718913 := by
    simpa [prefixWord, tailWord_1718913, baseEnd_1718913] using wordTrace_append hprefix tailTrace_1718913
  have hstable : (prefixWord ++ tailWord_1718913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718913).length < 2 ^ (prefixWord ++ tailWord_1718913).sum := by decide
  have hdescent : baseEnd_1718913 < baseStart_1718913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718930 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1718930 : Nat := 118140960795 + 1718930 * 2 ^ 59
def prefixEnd_1718930 : Nat := 4983230072969 + 3 ^ 40 * 1718930 * 2
def baseEnd_1718930 : Nat := 882637301433064912169791

theorem tailTrace_1718930 : CollatzResearch.WordTrace tailWord_1718930 prefixEnd_1718930 882637301433064912169791 := by
  unfold tailWord_1718930
  simp only [CollatzResearch.WordTrace]
  refine ⟨15673631915654413679204561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41796351775078436477878829 15673631915654413679204561)
  ·
    refine ⟨11755223936740810259403421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15673631915654413679204561 11755223936740810259403421)
    ·
      refine ⟨4408208976277803847276283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11755223936740810259403421 4408208976277803847276283)
      ·
        refine ⟨6612313464416705770914425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408208976277803847276283 6612313464416705770914425)
        ·
          refine ⟨4959235098312529328185819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6612313464416705770914425 4959235098312529328185819)
          ·
            refine ⟨7438852647468793992278729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959235098312529328185819 7438852647468793992278729)
            ·
              refine ⟨5579139485601595494209047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438852647468793992278729 5579139485601595494209047)
              ·
                refine ⟨8368709228402393241313571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579139485601595494209047 8368709228402393241313571)
                ·
                  refine ⟨12553063842603589861970357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8368709228402393241313571 12553063842603589861970357)
                  ·
                    refine ⟨1176849735244086549559721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12553063842603589861970357 1176849735244086549559721)
                    ·
                      refine ⟨882637301433064912169791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176849735244086549559721 882637301433064912169791)
                      ·
                        rfl

theorem cell23_1718930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1718930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718930 prefixEnd_1718930 := by exact prefixLift 1718930
  have htrace : WordTrace (prefixWord ++ tailWord_1718930) baseStart_1718930 baseEnd_1718930 := by
    simpa [prefixWord, tailWord_1718930, baseEnd_1718930] using wordTrace_append hprefix tailTrace_1718930
  have hstable : (prefixWord ++ tailWord_1718930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718930).length < 2 ^ (prefixWord ++ tailWord_1718930).sum := by decide
  have hdescent : baseEnd_1718930 < baseStart_1718930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718936 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1718936 : Nat := 118140960795 + 1718936 * 2 ^ 59
def prefixEnd_1718936 : Nat := 4983230072969 + 3 ^ 40 * 1718936 * 2
def baseEnd_1718936 : Nat := 294213460772330629564921

theorem tailTrace_1718936 : CollatzResearch.WordTrace tailWord_1718936 prefixEnd_1718936 294213460772330629564921 := by
  unfold tailWord_1718936
  simp only [CollatzResearch.WordTrace]
  refine ⟨31347373250297958870768331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41796497667063945161024441 31347373250297958870768331)
  ·
    refine ⟨47021059875446938306152497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31347373250297958870768331 47021059875446938306152497)
    ·
      refine ⟨35265794906585203729614373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47021059875446938306152497 35265794906585203729614373)
      ·
        refine ⟨6612336544984725699302695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35265794906585203729614373 6612336544984725699302695)
        ·
          refine ⟨9918504817477088548954043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612336544984725699302695 9918504817477088548954043)
          ·
            refine ⟨14877757226215632823431065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918504817477088548954043 14877757226215632823431065)
            ·
              refine ⟨11158317919661724617573299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14877757226215632823431065 11158317919661724617573299)
              ·
                refine ⟨16737476879492586926359949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11158317919661724617573299 16737476879492586926359949)
                ·
                  refine ⟨6276553829809720097384981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16737476879492586926359949 6276553829809720097384981)
                  ·
                    refine ⟨294213460772330629564921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6276553829809720097384981 294213460772330629564921)
                    ·
                      rfl

theorem cell23_1718936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1718936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718936 prefixEnd_1718936 := by exact prefixLift 1718936
  have htrace : WordTrace (prefixWord ++ tailWord_1718936) baseStart_1718936 baseEnd_1718936 := by
    simpa [prefixWord, tailWord_1718936, baseEnd_1718936] using wordTrace_append hprefix tailTrace_1718936
  have hstable : (prefixWord ++ tailWord_1718936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718936).length < 2 ^ (prefixWord ++ tailWord_1718936).sum := by decide
  have hdescent : baseEnd_1718936 < baseStart_1718936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718977 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1718977 : Nat := 118140960795 + 1718977 * 2 ^ 59
def prefixEnd_1718977 : Nat := 4983230072969 + 3 ^ 40 * 1718977 * 2
def baseEnd_1718977 : Nat := 882661435023826228282075

theorem tailTrace_1718977 : CollatzResearch.WordTrace tailWord_1718977 prefixEnd_1718977 882661435023826228282075 := by
  unfold tailWord_1718977
  simp only [CollatzResearch.WordTrace]
  refine ⟨62696241893447381743779185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41797494595631587829186123 62696241893447381743779185)
  ·
    refine ⟨47022181420085536307834389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62696241893447381743779185 47022181420085536307834389)
    ·
      refine ⟨2204164754066509514429737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47022181420085536307834389 2204164754066509514429737)
      ·
        refine ⟨1653123565549882135822303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2204164754066509514429737 1653123565549882135822303)
        ·
          refine ⟨2479685348324823203733455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653123565549882135822303 2479685348324823203733455)
          ·
            refine ⟨3719528022487234805600183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479685348324823203733455 3719528022487234805600183)
            ·
              refine ⟨5579292033730852208400275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719528022487234805600183 5579292033730852208400275)
              ·
                refine ⟨8368938050596278312600413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579292033730852208400275 8368938050596278312600413)
                ·
                  refine ⟨3138351768973604367225155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8368938050596278312600413 3138351768973604367225155)
                  ·
                    refine ⟨4707527653460406550837733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138351768973604367225155 4707527653460406550837733)
                    ·
                      refine ⟨882661435023826228282075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4707527653460406550837733 882661435023826228282075)
                      ·
                        rfl

theorem cell23_1718977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1718977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718977 prefixEnd_1718977 := by exact prefixLift 1718977
  have htrace : WordTrace (prefixWord ++ tailWord_1718977) baseStart_1718977 baseEnd_1718977 := by
    simpa [prefixWord, tailWord_1718977, baseEnd_1718977] using wordTrace_append hprefix tailTrace_1718977
  have hstable : (prefixWord ++ tailWord_1718977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718977).length < 2 ^ (prefixWord ++ tailWord_1718977).sum := by decide
  have hdescent : baseEnd_1718977 < baseStart_1718977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718980 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1718980 : Nat := 118140960795 + 1718980 * 2 ^ 59
def prefixEnd_1718980 : Nat := 4983230072969 + 3 ^ 40 * 1718980 * 2
def baseEnd_1718980 : Nat := 882662975465789716544561

theorem tailTrace_1718980 : CollatzResearch.WordTrace tailWord_1718980 prefixEnd_1718980 882662975465789716544561 := by
  unfold tailWord_1718980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31348175656218256628069197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41797567541624342170758929 31348175656218256628069197)
  ·
    refine ⟨11755565871081846235525949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31348175656218256628069197 11755565871081846235525949)
    ·
      refine ⟨4408337201655692338322231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11755565871081846235525949 4408337201655692338322231)
      ·
        refine ⟨6612505802483538507483347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408337201655692338322231 6612505802483538507483347)
        ·
          refine ⟨9918758703725307761225021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612505802483538507483347 9918758703725307761225021)
          ·
            refine ⟨3719534513896990410459383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9918758703725307761225021 3719534513896990410459383)
            ·
              refine ⟨5579301770845485615689075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719534513896990410459383 5579301770845485615689075)
              ·
                refine ⟨8368952656268228423533613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579301770845485615689075 8368952656268228423533613)
                ·
                  refine ⟨3138357246100585658825105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8368952656268228423533613 3138357246100585658825105)
                  ·
                    refine ⟨2353767934575439244118829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3138357246100585658825105 2353767934575439244118829)
                    ·
                      refine ⟨882662975465789716544561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2353767934575439244118829 882662975465789716544561)
                      ·
                        rfl

theorem cell23_1718980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1718980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718980 prefixEnd_1718980 := by exact prefixLift 1718980
  have htrace : WordTrace (prefixWord ++ tailWord_1718980) baseStart_1718980 baseEnd_1718980 := by
    simpa [prefixWord, tailWord_1718980, baseEnd_1718980] using wordTrace_append hprefix tailTrace_1718980
  have hstable : (prefixWord ++ tailWord_1718980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718980).length < 2 ^ (prefixWord ++ tailWord_1718980).sum := by decide
  have hdescent : baseEnd_1718980 < baseStart_1718980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718993 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_1718993 : Nat := 118140960795 + 1718993 * 2 ^ 59
def prefixEnd_1718993 : Nat := 4983230072969 + 3 ^ 40 * 1718993 * 2
def baseEnd_1718993 : Nat := 882669650714298165682001

theorem tailTrace_1718993 : CollatzResearch.WordTrace tailWord_1718993 prefixEnd_1718993 882669650714298165682001 := by
  unfold tailWord_1718993
  simp only [CollatzResearch.WordTrace]
  refine ⟨62696825461389416476361633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41797883640926277650907755 62696825461389416476361633)
  ·
    refine ⟨47022619096042062357271225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62696825461389416476361633 47022619096042062357271225)
    ·
      refine ⟨35266964322031546767953419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47022619096042062357271225 35266964322031546767953419)
      ·
        refine ⟨52900446483047320151930129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35266964322031546767953419 52900446483047320151930129)
        ·
          refine ⟨39675334862285490113947597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52900446483047320151930129 39675334862285490113947597)
          ·
            refine ⟨14878250573357058792730349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39675334862285490113947597 14878250573357058792730349)
            ·
              refine ⟨5579343965008897047273881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14878250573357058792730349 5579343965008897047273881)
              ·
                refine ⟨4184507973756672785455411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579343965008897047273881 4184507973756672785455411)
                ·
                  refine ⟨6276761960635009178183117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184507973756672785455411 6276761960635009178183117)
                  ·
                    refine ⟨2353785735238128441818669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6276761960635009178183117 2353785735238128441818669)
                    ·
                      refine ⟨882669650714298165682001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2353785735238128441818669 882669650714298165682001)
                      ·
                        rfl

theorem cell23_1718993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_1718993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718993 prefixEnd_1718993 := by exact prefixLift 1718993
  have htrace : WordTrace (prefixWord ++ tailWord_1718993) baseStart_1718993 baseEnd_1718993 := by
    simpa [prefixWord, tailWord_1718993, baseEnd_1718993] using wordTrace_append hprefix tailTrace_1718993
  have hstable : (prefixWord ++ tailWord_1718993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718993).length < 2 ^ (prefixWord ++ tailWord_1718993).sum := by decide
  have hdescent : baseEnd_1718993 < baseStart_1718993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718997 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1718997 : Nat := 118140960795 + 1718997 * 2 ^ 59
def prefixEnd_1718997 : Nat := 4983230072969 + 3 ^ 40 * 1718997 * 2
def baseEnd_1718997 : Nat := 882671704636916150031983

theorem tailTrace_1718997 : CollatzResearch.WordTrace tailWord_1718997 prefixEnd_1718997 882671704636916150031983 := by
  unfold tailWord_1718997
  simp only [CollatzResearch.WordTrace]
  refine ⟨62696971353374925159507245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41797980902249950106338163 62696971353374925159507245)
  ·
    refine ⟨23511364257515596934815217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62696971353374925159507245 23511364257515596934815217)
    ·
      refine ⟨17633523193136697701111413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23511364257515596934815217 17633523193136697701111413)
      ·
        refine ⟨1653142799356565409479195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17633523193136697701111413 1653142799356565409479195)
        ·
          refine ⟨2479714199034848114218793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653142799356565409479195 2479714199034848114218793)
          ·
            refine ⟨1859785649276136085664095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479714199034848114218793 1859785649276136085664095)
            ·
              refine ⟨2789678473914204128496143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859785649276136085664095 2789678473914204128496143)
              ·
                refine ⟨4184517710871306192744215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789678473914204128496143 4184517710871306192744215)
                ·
                  refine ⟨6276776566306959289116323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184517710871306192744215 6276776566306959289116323)
                  ·
                    refine ⟨9415164849460438933674485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6276776566306959289116323 9415164849460438933674485)
                    ·
                      refine ⟨882671704636916150031983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9415164849460438933674485 882671704636916150031983)
                      ·
                        rfl

theorem cell23_1718997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1718997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1718997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1718997 prefixEnd_1718997 := by exact prefixLift 1718997
  have htrace : WordTrace (prefixWord ++ tailWord_1718997) baseStart_1718997 baseEnd_1718997 := by
    simpa [prefixWord, tailWord_1718997, baseEnd_1718997] using wordTrace_append hprefix tailTrace_1718997
  have hstable : (prefixWord ++ tailWord_1718997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718997).length < 2 ^ (prefixWord ++ tailWord_1718997).sum := by decide
  have hdescent : baseEnd_1718997 < baseStart_1718997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719011 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1719011 : Nat := 118140960795 + 1719011 * 2 ^ 59
def prefixEnd_1719011 : Nat := 4983230072969 + 3 ^ 40 * 1719011 * 2
def baseEnd_1719011 : Nat := 882678893366079095256919

theorem tailTrace_1719011 : CollatzResearch.WordTrace tailWord_1719011 prefixEnd_1719011 882678893366079095256919 := by
  unfold tailWord_1719011
  simp only [CollatzResearch.WordTrace]
  refine ⟨62697481975324205550516887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41798321316882803700344591 62697481975324205550516887)
  ·
    refine ⟨94046222962986308325775331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62697481975324205550516887 94046222962986308325775331)
    ·
      refine ⟨141069334444479462488662997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94046222962986308325775331 141069334444479462488662997)
      ·
        refine ⟨3306312526042487402078039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 141069334444479462488662997 3306312526042487402078039)
        ·
          refine ⟨4959468789063731103117059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306312526042487402078039 4959468789063731103117059)
          ·
            refine ⟨7439203183595596654675589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959468789063731103117059 7439203183595596654675589)
            ·
              refine ⟨1394850596924174372751673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7439203183595596654675589 1394850596924174372751673)
              ·
                refine ⟨1046137947693130779563755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394850596924174372751673 1046137947693130779563755)
                ·
                  refine ⟨1569206921539696169345633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046137947693130779563755 1569206921539696169345633)
                  ·
                    refine ⟨1176905191154772127009225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569206921539696169345633 1176905191154772127009225)
                    ·
                      refine ⟨882678893366079095256919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176905191154772127009225 882678893366079095256919)
                      ·
                        rfl

theorem cell23_1719011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1719011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719011 prefixEnd_1719011 := by exact prefixLift 1719011
  have htrace : WordTrace (prefixWord ++ tailWord_1719011) baseStart_1719011 baseEnd_1719011 := by
    simpa [prefixWord, tailWord_1719011, baseEnd_1719011] using wordTrace_append hprefix tailTrace_1719011
  have hstable : (prefixWord ++ tailWord_1719011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719011).length < 2 ^ (prefixWord ++ tailWord_1719011).sum := by decide
  have hdescent : baseEnd_1719011 < baseStart_1719011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719050 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_1719050 : Nat := 118140960795 + 1719050 * 2 ^ 59
def prefixEnd_1719050 : Nat := 4983230072969 + 3 ^ 40 * 1719050 * 2
def baseEnd_1719050 : Nat := 882698919111604442669239

theorem tailTrace_1719050 : CollatzResearch.WordTrace tailWord_1719050 prefixEnd_1719050 882698919111604442669239 := by
  unfold tailWord_1719050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674726105545728802796651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41799269614788610140791069 15674726105545728802796651)
  ·
    refine ⟨23512089158318593204194977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674726105545728802796651 23512089158318593204194977)
    ·
      refine ⟨17634066868738944903146233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23512089158318593204194977 17634066868738944903146233)
      ·
        refine ⟨13225550151554208677359675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17634066868738944903146233 13225550151554208677359675)
        ·
          refine ⟨19838325227331313016039513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225550151554208677359675 19838325227331313016039513)
          ·
            refine ⟨14878743920498484762029635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19838325227331313016039513 14878743920498484762029635)
            ·
              refine ⟨22318115880747727143044453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14878743920498484762029635 22318115880747727143044453)
              ·
                refine ⟨4184646727640198839320835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22318115880747727143044453 4184646727640198839320835)
                ·
                  refine ⟨6276970091460298258981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184646727640198839320835 6276970091460298258981253)
                  ·
                    refine ⟨1176931892148805923558985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276970091460298258981253 1176931892148805923558985)
                    ·
                      refine ⟨882698919111604442669239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176931892148805923558985 882698919111604442669239)
                      ·
                        rfl

theorem cell23_1719050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_1719050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719050 prefixEnd_1719050 := by exact prefixLift 1719050
  have htrace : WordTrace (prefixWord ++ tailWord_1719050) baseStart_1719050 baseEnd_1719050 := by
    simpa [prefixWord, tailWord_1719050, baseEnd_1719050] using wordTrace_append hprefix tailTrace_1719050
  have hstable : (prefixWord ++ tailWord_1719050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719050).length < 2 ^ (prefixWord ++ tailWord_1719050).sum := by decide
  have hdescent : baseEnd_1719050 < baseStart_1719050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719073 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 7]
def baseStart_1719073 : Nat := 118140960795 + 1719073 * 2 ^ 59
def prefixEnd_1719073 : Nat := 4983230072969 + 3 ^ 40 * 1719073 * 2
def baseEnd_1719073 : Nat := 98078969907406428075737

theorem tailTrace_1719073 : CollatzResearch.WordTrace tailWord_1719073 prefixEnd_1719073 98078969907406428075737 := by
  unfold tailWord_1719073
  simp only [CollatzResearch.WordTrace]
  refine ⟨62699743301099590139273873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41799828867399726759515915 62699743301099590139273873)
  ·
    refine ⟨47024807475824692604455405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62699743301099590139273873 47024807475824692604455405)
    ·
      refine ⟨17634302803434259726670777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47024807475824692604455405 17634302803434259726670777)
      ·
        refine ⟨13225727102575694795003083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17634302803434259726670777 13225727102575694795003083)
        ·
          refine ⟨19838590653863542192504625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13225727102575694795003083 19838590653863542192504625)
          ·
            refine ⟨14878942990397656644378469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19838590653863542192504625 14878942990397656644378469)
            ·
              refine ⟨2789801810699560620820963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14878942990397656644378469 2789801810699560620820963)
              ·
                refine ⟨4184702716049340931231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789801810699560620820963 4184702716049340931231445)
                ·
                  refine ⟨98078969907406428075737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4184702716049340931231445 98078969907406428075737)
                  ·
                    rfl

theorem cell23_1719073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_1719073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719073 prefixEnd_1719073 := by exact prefixLift 1719073
  have htrace : WordTrace (prefixWord ++ tailWord_1719073) baseStart_1719073 baseEnd_1719073 := by
    simpa [prefixWord, tailWord_1719073, baseEnd_1719073] using wordTrace_append hprefix tailTrace_1719073
  have hstable : (prefixWord ++ tailWord_1719073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719073).length < 2 ^ (prefixWord ++ tailWord_1719073).sum := by decide
  have hdescent : baseEnd_1719073 < baseStart_1719073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719084 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_1719084 : Nat := 118140960795 + 1719084 * 2 ^ 59
def prefixEnd_1719084 : Nat := 4983230072969 + 3 ^ 40 * 1719084 * 2
def baseEnd_1719084 : Nat := 882716377453857309644083

theorem tailTrace_1719084 : CollatzResearch.WordTrace tailWord_1719084 prefixEnd_1719084 882716377453857309644083 := by
  unfold tailWord_1719084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350072252029869508962153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41800096336039826011949537 31350072252029869508962153)
  ·
    refine ⟨23512554189022402131721615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31350072252029869508962153 23512554189022402131721615)
    ·
      refine ⟨35268831283533603197582423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23512554189022402131721615 35268831283533603197582423)
      ·
        refine ⟨52903246925300404796373635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35268831283533603197582423 52903246925300404796373635)
        ·
          refine ⟨79354870387950607194560453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52903246925300404796373635 79354870387950607194560453)
          ·
            refine ⟨14879038197740738848980085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79354870387950607194560453 14879038197740738848980085)
            ·
              refine ⟨1394909831038194267091883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14879038197740738848980085 1394909831038194267091883)
              ·
                refine ⟨2092364746557291400637825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394909831038194267091883 2092364746557291400637825)
                ·
                  refine ⟨1569273559917968550478369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2092364746557291400637825 1569273559917968550478369)
                  ·
                    refine ⟨1176955169938476412858777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569273559917968550478369 1176955169938476412858777)
                    ·
                      refine ⟨882716377453857309644083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1176955169938476412858777 882716377453857309644083)
                      ·
                        rfl

theorem cell23_1719084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_1719084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719084 prefixEnd_1719084 := by exact prefixLift 1719084
  have htrace : WordTrace (prefixWord ++ tailWord_1719084) baseStart_1719084 baseEnd_1719084 := by
    simpa [prefixWord, tailWord_1719084, baseEnd_1719084] using wordTrace_append hprefix tailTrace_1719084
  have hstable : (prefixWord ++ tailWord_1719084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719084).length < 2 ^ (prefixWord ++ tailWord_1719084).sum := by decide
  have hdescent : baseEnd_1719084 < baseStart_1719084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719103 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 7]
def baseStart_1719103 : Nat := 118140960795 + 1719103 * 2 ^ 59
def prefixEnd_1719103 : Nat := 4983230072969 + 3 ^ 40 * 1719103 * 2
def baseEnd_1719103 : Nat := 294242044528764245102165

theorem tailTrace_1719103 : CollatzResearch.WordTrace tailWord_1719103 prefixEnd_1719103 294242044528764245102165 := by
  unfold tailWord_1719103
  simp only [CollatzResearch.WordTrace]
  refine ⟨62700837490990905262865963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41800558327327270175243975 62700837490990905262865963)
  ·
    refine ⟨94051256236486357894298945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62700837490990905262865963 94051256236486357894298945)
    ·
      refine ⟨70538442177364768420724209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94051256236486357894298945 70538442177364768420724209)
      ·
        refine ⟨52903831633023576315543157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70538442177364768420724209 52903831633023576315543157)
        ·
          refine ⟨4959734215595960279582171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52903831633023576315543157 4959734215595960279582171)
          ·
            refine ⟨7439601323393940419373257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959734215595960279582171 7439601323393940419373257)
            ·
              refine ⟨5579700992545455314529943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7439601323393940419373257 5579700992545455314529943)
              ·
                refine ⟨8369551488818182971794915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579700992545455314529943 8369551488818182971794915)
                ·
                  refine ⟨12554327233227274457692373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8369551488818182971794915 12554327233227274457692373)
                  ·
                    refine ⟨294242044528764245102165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12554327233227274457692373 294242044528764245102165)
                    ·
                      rfl

theorem cell23_1719103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_1719103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719103 prefixEnd_1719103 := by exact prefixLift 1719103
  have htrace : WordTrace (prefixWord ++ tailWord_1719103) baseStart_1719103 baseEnd_1719103 := by
    simpa [prefixWord, tailWord_1719103, baseEnd_1719103] using wordTrace_append hprefix tailTrace_1719103
  have hstable : (prefixWord ++ tailWord_1719103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719103).length < 2 ^ (prefixWord ++ tailWord_1719103).sum := by decide
  have hdescent : baseEnd_1719103 < baseStart_1719103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719124 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1719124 : Nat := 118140960795 + 1719124 * 2 ^ 59
def prefixEnd_1719124 : Nat := 4983230072969 + 3 ^ 40 * 1719124 * 2
def baseEnd_1719124 : Nat := 98081879631115239238211

theorem tailTrace_1719124 : CollatzResearch.WordTrace tailWord_1719124 prefixEnd_1719124 98081879631115239238211 := by
  unfold tailWord_1719124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350801711957412924690213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41801068949276550566253617 31350801711957412924690213)
  ·
    refine ⟨5878275320992014923379415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31350801711957412924690213 5878275320992014923379415)
    ·
      refine ⟨8817412981488022385069123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5878275320992014923379415 8817412981488022385069123)
      ·
        refine ⟨13226119472232033577603685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817412981488022385069123 13226119472232033577603685)
        ·
          refine ⟨2479897401043506295800691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13226119472232033577603685 2479897401043506295800691)
          ·
            refine ⟨3719846101565259443701037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479897401043506295800691 3719846101565259443701037)
            ·
              refine ⟨1394942288086972291387889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719846101565259443701037 1394942288086972291387889)
              ·
                refine ⟨1046206716065229218540917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394942288086972291387889 1046206716065229218540917)
                ·
                  refine ⟨98081879631115239238211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046206716065229218540917 98081879631115239238211)
                  ·
                    rfl

theorem cell23_1719124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1719124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719124 prefixEnd_1719124 := by exact prefixLift 1719124
  have htrace : WordTrace (prefixWord ++ tailWord_1719124) baseStart_1719124 baseEnd_1719124 := by
    simpa [prefixWord, tailWord_1719124, baseEnd_1719124] using wordTrace_append hprefix tailTrace_1719124
  have hstable : (prefixWord ++ tailWord_1719124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719124).length < 2 ^ (prefixWord ++ tailWord_1719124).sum := by decide
  have hdescent : baseEnd_1719124 < baseStart_1719124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719157 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1719157 : Nat := 118140960795 + 1719157 * 2 ^ 59
def prefixEnd_1719157 : Nat := 4983230072969 + 3 ^ 40 * 1719157 * 2
def baseEnd_1719157 : Nat := 882753861541635524031247

theorem tailTrace_1719157 : CollatzResearch.WordTrace tailWord_1719157 prefixEnd_1719157 882753861541635524031247 := by
  unfold tailWord_1719157
  simp only [CollatzResearch.WordTrace]
  refine ⟨62702807032795272485331725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41801871355196848323554483 62702807032795272485331725)
  ·
    refine ⟨23513552637298227181999397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62702807032795272485331725 23513552637298227181999397)
    ·
      refine ⟨4408791119493417596624887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23513552637298227181999397 4408791119493417596624887)
      ·
        refine ⟨6613186679240126394937331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408791119493417596624887 6613186679240126394937331)
        ·
          refine ⟨9919780018860189592405997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613186679240126394937331 9919780018860189592405997)
          ·
            refine ⟨3719917507072571097152249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9919780018860189592405997 3719917507072571097152249)
            ·
              refine ⟨2789938130304428322864187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3719917507072571097152249 2789938130304428322864187)
              ·
                refine ⟨4184907195456642484296281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789938130304428322864187 4184907195456642484296281)
                ·
                  refine ⟨3138680396592481863222211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184907195456642484296281 3138680396592481863222211)
                  ·
                    refine ⟨4708020594888722794833317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138680396592481863222211 4708020594888722794833317)
                    ·
                      refine ⟨882753861541635524031247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4708020594888722794833317 882753861541635524031247)
                      ·
                        rfl

theorem cell23_1719157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1719157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719157 prefixEnd_1719157 := by exact prefixLift 1719157
  have htrace : WordTrace (prefixWord ++ tailWord_1719157) baseStart_1719157 baseEnd_1719157 := by
    simpa [prefixWord, tailWord_1719157, baseEnd_1719157] using wordTrace_append hprefix tailTrace_1719157
  have hstable : (prefixWord ++ tailWord_1719157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719157).length < 2 ^ (prefixWord ++ tailWord_1719157).sum := by decide
  have hdescent : baseEnd_1719157 < baseStart_1719157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719224 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 1, 1, 3]
def baseStart_1719224 : Nat := 118140960795 + 1719224 * 2 ^ 59
def prefixEnd_1719224 : Nat := 4983230072969 + 3 ^ 40 * 1719224 * 2
def baseEnd_1719224 : Nat := 882788264745486761893439

theorem tailTrace_1719224 : CollatzResearch.WordTrace tailWord_1719224 prefixEnd_1719224 882788264745486761893439 := by
  unfold tailWord_1719224
  simp only [CollatzResearch.WordTrace]
  refine ⟨31352625361776271464010363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41803500482368361952013817 31352625361776271464010363)
  ·
    refine ⟨47028938042664407196015545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31352625361776271464010363 47028938042664407196015545)
    ·
      refine ⟨35271703531998305397011659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47028938042664407196015545 35271703531998305397011659)
      ·
        refine ⟨52907555297997458095517489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35271703531998305397011659 52907555297997458095517489)
        ·
          refine ⟨39680666473498093571638117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52907555297997458095517489 39680666473498093571638117)
          ·
            refine ⟨7440124963780892544682147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39680666473498093571638117 7440124963780892544682147)
            ·
              refine ⟨11160187445671338817023221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440124963780892544682147 11160187445671338817023221)
              ·
                refine ⟨1046267573031688014095927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11160187445671338817023221 1046267573031688014095927)
                ·
                  refine ⟨1569401359547532021143891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046267573031688014095927 1569401359547532021143891)
                  ·
                    refine ⟨2354102039321298031715837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1569401359547532021143891 2354102039321298031715837)
                    ·
                      refine ⟨882788264745486761893439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354102039321298031715837 882788264745486761893439)
                      ·
                        rfl

theorem cell23_1719224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_1719224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719224 prefixEnd_1719224 := by exact prefixLift 1719224
  have htrace : WordTrace (prefixWord ++ tailWord_1719224) baseStart_1719224 baseEnd_1719224 := by
    simpa [prefixWord, tailWord_1719224, baseEnd_1719224] using wordTrace_append hprefix tailTrace_1719224
  have hstable : (prefixWord ++ tailWord_1719224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719224).length < 2 ^ (prefixWord ++ tailWord_1719224).sum := by decide
  have hdescent : baseEnd_1719224 < baseStart_1719224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719257 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_1719257 : Nat := 118140960795 + 1719257 * 2 ^ 59
def prefixEnd_1719257 : Nat := 4983230072969 + 3 ^ 40 * 1719257 * 2
def baseEnd_1719257 : Nat := 294268403202361710926929

theorem tailTrace_1719257 : CollatzResearch.WordTrace tailWord_1719257 prefixEnd_1719257 294268403202361710926929 := by
  unfold tailWord_1719257
  simp only [CollatzResearch.WordTrace]
  refine ⟨62706454332432989563972025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41804302888288659709314683 62706454332432989563972025)
  ·
    refine ⟨47029840749324742172979019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62706454332432989563972025 47029840749324742172979019)
    ·
      refine ⟨70544761123987113259468529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47029840749324742172979019 70544761123987113259468529)
      ·
        refine ⟨52908570842990334944601397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70544761123987113259468529 52908570842990334944601397)
        ·
          refine ⟨4960178516530343901056381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52908570842990334944601397 4960178516530343901056381)
          ·
            refine ⟨1860066943698878962896143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4960178516530343901056381 1860066943698878962896143)
            ·
              refine ⟨2790100415548318444344215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860066943698878962896143 2790100415548318444344215)
              ·
                refine ⟨4185150623322477666516323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790100415548318444344215 4185150623322477666516323)
                ·
                  refine ⟨6277725934983716499774485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185150623322477666516323 6277725934983716499774485)
                  ·
                    refine ⟨294268403202361710926929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6277725934983716499774485 294268403202361710926929)
                    ·
                      rfl

theorem cell23_1719257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_1719257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719257 prefixEnd_1719257 := by exact prefixLift 1719257
  have htrace : WordTrace (prefixWord ++ tailWord_1719257) baseStart_1719257 baseEnd_1719257 := by
    simpa [prefixWord, tailWord_1719257, baseEnd_1719257] using wordTrace_append hprefix tailTrace_1719257
  have hstable : (prefixWord ++ tailWord_1719257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719257).length < 2 ^ (prefixWord ++ tailWord_1719257).sum := by decide
  have hdescent : baseEnd_1719257 < baseStart_1719257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719273 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_1719273 : Nat := 118140960795 + 1719273 * 2 ^ 59
def prefixEnd_1719273 : Nat := 4983230072969 + 3 ^ 40 * 1719273 * 2
def baseEnd_1719273 : Nat := 882813425297557070180713

theorem tailTrace_1719273 : CollatzResearch.WordTrace tailWord_1719273 prefixEnd_1719273 882813425297557070180713 := by
  unfold tailWord_1719273
  simp only [CollatzResearch.WordTrace]
  refine ⟨62707037900375024296554473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41804691933583349531036315 62707037900375024296554473)
  ·
    refine ⟨47030278425281268222415855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62707037900375024296554473 47030278425281268222415855)
    ·
      refine ⟨70545417637921902333623783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47030278425281268222415855 70545417637921902333623783)
      ·
        refine ⟨105818126456882853500435675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70545417637921902333623783 105818126456882853500435675)
        ·
          refine ⟨158727189685324280250653513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105818126456882853500435675 158727189685324280250653513)
          ·
            refine ⟨119045392263993210187990135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158727189685324280250653513 119045392263993210187990135)
            ·
              refine ⟨178568088395989815281985203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119045392263993210187990135 178568088395989815281985203)
              ·
                refine ⟨267852132593984722922977805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178568088395989815281985203 267852132593984722922977805)
                ·
                  refine ⟨100444549722744271096116677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267852132593984722922977805 100444549722744271096116677)
                  ·
                    refine ⟨18833353073014550830521877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100444549722744271096116677 18833353073014550830521877)
                    ·
                      refine ⟨882813425297557070180713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18833353073014550830521877 882813425297557070180713)
                      ·
                        rfl

theorem cell23_1719273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_1719273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719273 prefixEnd_1719273 := by exact prefixLift 1719273
  have htrace : WordTrace (prefixWord ++ tailWord_1719273) baseStart_1719273 baseEnd_1719273 := by
    simpa [prefixWord, tailWord_1719273, baseEnd_1719273] using wordTrace_append hprefix tailTrace_1719273
  have hstable : (prefixWord ++ tailWord_1719273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719273).length < 2 ^ (prefixWord ++ tailWord_1719273).sum := by decide
  have hdescent : baseEnd_1719273 < baseStart_1719273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719280 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_1719280 : Nat := 118140960795 + 1719280 * 2 ^ 59
def prefixEnd_1719280 : Nat := 4983230072969 + 3 ^ 40 * 1719280 * 2
def baseEnd_1719280 : Nat := 882817019662138542793181

theorem tailTrace_1719280 : CollatzResearch.WordTrace tailWord_1719280 prefixEnd_1719280 882817019662138542793181 := by
  unfold tailWord_1719280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31353646605674832246029647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41804862140899776328039529 31353646605674832246029647)
  ·
    refine ⟨47030469908512248369044471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31353646605674832246029647 47030469908512248369044471)
    ·
      refine ⟨70545704862768372553566707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47030469908512248369044471 70545704862768372553566707)
      ·
        refine ⟨105818557294152558830350061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70545704862768372553566707 105818557294152558830350061)
        ·
          refine ⟨39681958985307209561381273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105818557294152558830350061 39681958985307209561381273)
          ·
            refine ⟨29761469238980407171035955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39681958985307209561381273 29761469238980407171035955)
            ·
              refine ⟨44642203858470610756553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29761469238980407171035955 44642203858470610756553933)
              ·
                refine ⟨16740826446926479033707725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44642203858470610756553933 16740826446926479033707725)
                ·
                  refine ⟨6277809917597429637640397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16740826446926479033707725 6277809917597429637640397)
                  ·
                    refine ⟨2354178719099036114115149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6277809917597429637640397 2354178719099036114115149)
                    ·
                      refine ⟨882817019662138542793181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354178719099036114115149 882817019662138542793181)
                      ·
                        rfl

theorem cell23_1719280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_1719280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719280 prefixEnd_1719280 := by exact prefixLift 1719280
  have htrace : WordTrace (prefixWord ++ tailWord_1719280) baseStart_1719280 baseEnd_1719280 := by
    simpa [prefixWord, tailWord_1719280, baseEnd_1719280] using wordTrace_append hprefix tailTrace_1719280
  have hstable : (prefixWord ++ tailWord_1719280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719280).length < 2 ^ (prefixWord ++ tailWord_1719280).sum := by decide
  have hdescent : baseEnd_1719280 < baseStart_1719280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719283 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 9]
def baseStart_1719283 : Nat := 118140960795 + 1719283 * 2 ^ 59
def prefixEnd_1719283 : Nat := 4983230072969 + 3 ^ 40 * 1719283 * 2
def baseEnd_1719283 : Nat := 294272853368034010351889

theorem tailTrace_1719283 : CollatzResearch.WordTrace tailWord_1719283 prefixEnd_1719283 294272853368034010351889 := by
  unfold tailWord_1719283
  simp only [CollatzResearch.WordTrace]
  refine ⟨62707402630338796004418503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41804935086892530669612335 62707402630338796004418503)
  ·
    refine ⟨94061103945508194006627755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62707402630338796004418503 94061103945508194006627755)
    ·
      refine ⟨141091655918262291009941633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94061103945508194006627755 141091655918262291009941633)
      ·
        refine ⟨105818741938696718257456225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141091655918262291009941633 105818741938696718257456225)
        ·
          refine ⟨79364056454022538693092169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105818741938696718257456225 79364056454022538693092169)
          ·
            refine ⟨59523042340516904019819127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79364056454022538693092169 59523042340516904019819127)
            ·
              refine ⟨89284563510775356029728691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59523042340516904019819127 89284563510775356029728691)
              ·
                refine ⟨133926845266163034044593037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89284563510775356029728691 133926845266163034044593037)
                ·
                  refine ⟨50222566974811137766722389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133926845266163034044593037 50222566974811137766722389)
                  ·
                    refine ⟨294272853368034010351889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50222566974811137766722389 294272853368034010351889)
                    ·
                      rfl

theorem cell23_1719283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_1719283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719283 prefixEnd_1719283 := by exact prefixLift 1719283
  have htrace : WordTrace (prefixWord ++ tailWord_1719283) baseStart_1719283 baseEnd_1719283 := by
    simpa [prefixWord, tailWord_1719283, baseEnd_1719283] using wordTrace_append hprefix tailTrace_1719283
  have hstable : (prefixWord ++ tailWord_1719283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719283).length < 2 ^ (prefixWord ++ tailWord_1719283).sum := by decide
  have hdescent : baseEnd_1719283 < baseStart_1719283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719340 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1719340 : Nat := 118140960795 + 1719340 * 2 ^ 59
def prefixEnd_1719340 : Nat := 4983230072969 + 3 ^ 40 * 1719340 * 2
def baseEnd_1719340 : Nat := 882847828501408308042905

theorem tailTrace_1719340 : CollatzResearch.WordTrace tailWord_1719340 prefixEnd_1719340 882847828501408308042905 := by
  unfold tailWord_1719340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31354740795566147369621737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41806321060754863159495649 31354740795566147369621737)
  ·
    refine ⟨23516055596674610527216303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31354740795566147369621737 23516055596674610527216303)
    ·
      refine ⟨35274083395011915790824455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23516055596674610527216303 35274083395011915790824455)
      ·
        refine ⟨52911125092517873686236683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35274083395011915790824455 52911125092517873686236683)
        ·
          refine ⟨79366687638776810529355025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52911125092517873686236683 79366687638776810529355025)
          ·
            refine ⟨59525015729082607897016269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79366687638776810529355025 59525015729082607897016269)
            ·
              refine ⟨22321880898405977961381101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59525015729082607897016269 22321880898405977961381101)
              ·
                refine ⟨8370705336902241735517913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22321880898405977961381101 8370705336902241735517913)
                ·
                  refine ⟨6278029002676681301638435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8370705336902241735517913 6278029002676681301638435)
                  ·
                    refine ⟨9417043504015021952457653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278029002676681301638435 9417043504015021952457653)
                    ·
                      refine ⟨882847828501408308042905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9417043504015021952457653 882847828501408308042905)
                      ·
                        rfl

theorem cell23_1719340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1719340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719340 prefixEnd_1719340 := by exact prefixLift 1719340
  have htrace : WordTrace (prefixWord ++ tailWord_1719340) baseStart_1719340 baseEnd_1719340 := by
    simpa [prefixWord, tailWord_1719340, baseEnd_1719340] using wordTrace_append hprefix tailTrace_1719340
  have hstable : (prefixWord ++ tailWord_1719340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719340).length < 2 ^ (prefixWord ++ tailWord_1719340).sum := by decide
  have hdescent : baseEnd_1719340 < baseStart_1719340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719348 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1719348 : Nat := 118140960795 + 1719348 * 2 ^ 59
def prefixEnd_1719348 : Nat := 4983230072969 + 3 ^ 40 * 1719348 * 2
def baseEnd_1719348 : Nat := 882851936346644276742869

theorem tailTrace_1719348 : CollatzResearch.WordTrace tailWord_1719348 prefixEnd_1719348 882851936346644276742869 := by
  unfold tailWord_1719348
  simp only [CollatzResearch.WordTrace]
  refine ⟨31354886687551656052767349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41806515583402208070356465 31354886687551656052767349)
  ·
    refine ⟨2939520626957967754946939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31354886687551656052767349 2939520626957967754946939)
    ·
      refine ⟨4409280940436951632420409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939520626957967754946939 4409280940436951632420409)
      ·
        refine ⟨3306960705327713724315307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409280940436951632420409 3306960705327713724315307)
        ·
          refine ⟨4960441057991570586472961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306960705327713724315307 4960441057991570586472961)
          ·
            refine ⟨3720330793493677939854721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960441057991570586472961 3720330793493677939854721)
            ·
              refine ⟨2790248095120258454891041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3720330793493677939854721 2790248095120258454891041)
              ·
                refine ⟨2092686071340193841168281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790248095120258454891041 2092686071340193841168281)
                ·
                  refine ⟨1569514553505145380876211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2092686071340193841168281 1569514553505145380876211)
                  ·
                    refine ⟨2354271830257718071314317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1569514553505145380876211 2354271830257718071314317)
                    ·
                      refine ⟨882851936346644276742869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354271830257718071314317 882851936346644276742869)
                      ·
                        rfl

theorem cell23_1719348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1719348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719348 prefixEnd_1719348 := by exact prefixLift 1719348
  have htrace : WordTrace (prefixWord ++ tailWord_1719348) baseStart_1719348 baseEnd_1719348 := by
    simpa [prefixWord, tailWord_1719348, baseEnd_1719348] using wordTrace_append hprefix tailTrace_1719348
  have hstable : (prefixWord ++ tailWord_1719348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719348).length < 2 ^ (prefixWord ++ tailWord_1719348).sum := by decide
  have hdescent : baseEnd_1719348 < baseStart_1719348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719354 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_1719354 : Nat := 118140960795 + 1719354 * 2 ^ 59
def prefixEnd_1719354 : Nat := 4983230072969 + 3 ^ 40 * 1719354 * 2
def baseEnd_1719354 : Nat := 882855017230571253267841

theorem tailTrace_1719354 : CollatzResearch.WordTrace tailWord_1719354 prefixEnd_1719354 882855017230571253267841 := by
  unfold tailWord_1719354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677498053270393782563279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41806661475387716753502077 15677498053270393782563279)
  ·
    refine ⟨23516247079905590673844919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15677498053270393782563279 23516247079905590673844919)
    ·
      refine ⟨35274370619858386010767379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23516247079905590673844919 35274370619858386010767379)
      ·
        refine ⟨52911555929787579016151069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35274370619858386010767379 52911555929787579016151069)
        ·
          refine ⟨19841833473670342131056651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52911555929787579016151069 19841833473670342131056651)
          ·
            refine ⟨29762750210505513196584977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19841833473670342131056651 29762750210505513196584977)
            ·
              refine ⟨22322062657879134897438733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29762750210505513196584977 22322062657879134897438733)
              ·
                refine ⟨8370773496704675586539525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22322062657879134897438733 8370773496704675586539525)
                ·
                  refine ⟨1569520030632126672476161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8370773496704675586539525 1569520030632126672476161)
                  ·
                    refine ⟨1177140022974095004357121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569520030632126672476161 1177140022974095004357121)
                    ·
                      refine ⟨882855017230571253267841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177140022974095004357121 882855017230571253267841)
                      ·
                        rfl

theorem cell23_1719354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_1719354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719354 prefixEnd_1719354 := by exact prefixLift 1719354
  have htrace : WordTrace (prefixWord ++ tailWord_1719354) baseStart_1719354 baseEnd_1719354 := by
    simpa [prefixWord, tailWord_1719354, baseEnd_1719354] using wordTrace_append hprefix tailTrace_1719354
  have hstable : (prefixWord ++ tailWord_1719354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719354).length < 2 ^ (prefixWord ++ tailWord_1719354).sum := by decide
  have hdescent : baseEnd_1719354 < baseStart_1719354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719357 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1719357 : Nat := 118140960795 + 1719357 * 2 ^ 59
def prefixEnd_1719357 : Nat := 4983230072969 + 3 ^ 40 * 1719357 * 2
def baseEnd_1719357 : Nat := 882856557672534741530327

theorem tailTrace_1719357 : CollatzResearch.WordTrace tailWord_1719357 prefixEnd_1719357 882856557672534741530327 := by
  unfold tailWord_1719357
  simp only [CollatzResearch.WordTrace]
  refine ⟨62710101632070706642612325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41806734421380471095074883 62710101632070706642612325)
  ·
    refine ⟨11758144056013257495489811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62710101632070706642612325 11758144056013257495489811)
    ·
      refine ⟨17637216084019886243234717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11758144056013257495489811 17637216084019886243234717)
      ·
        refine ⟨6613956031507457341213019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17637216084019886243234717 6613956031507457341213019)
        ·
          refine ⟨9920934047261186011819529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613956031507457341213019 9920934047261186011819529)
          ·
            refine ⟨7440700535445889508864647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9920934047261186011819529 7440700535445889508864647)
            ·
              refine ⟨11161050803168834263296971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440700535445889508864647 11161050803168834263296971)
              ·
                refine ⟨16741576204753251394945457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161050803168834263296971 16741576204753251394945457)
                ·
                  refine ⟨12556182153564938546209093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16741576204753251394945457 12556182153564938546209093)
                  ·
                    refine ⟨2354284153793425977414205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12556182153564938546209093 2354284153793425977414205)
                    ·
                      refine ⟨882856557672534741530327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354284153793425977414205 882856557672534741530327)
                      ·
                        rfl

theorem cell23_1719357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1719357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719357 prefixEnd_1719357 := by exact prefixLift 1719357
  have htrace : WordTrace (prefixWord ++ tailWord_1719357) baseStart_1719357 baseEnd_1719357 := by
    simpa [prefixWord, tailWord_1719357, baseEnd_1719357] using wordTrace_append hprefix tailTrace_1719357
  have hstable : (prefixWord ++ tailWord_1719357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719357).length < 2 ^ (prefixWord ++ tailWord_1719357).sum := by decide
  have hdescent : baseEnd_1719357 < baseStart_1719357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719360 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 7]
def baseStart_1719360 : Nat := 118140960795 + 1719360 * 2 ^ 59
def prefixEnd_1719360 : Nat := 4983230072969 + 3 ^ 40 * 1719360 * 2
def baseEnd_1719360 : Nat := 98095344234944247754757

theorem tailTrace_1719360 : CollatzResearch.WordTrace tailWord_1719360 prefixEnd_1719360 98095344234944247754757 := by
  unfold tailWord_1719360
  simp only [CollatzResearch.WordTrace]
  refine ⟨31355105525529919077485767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41806807367373225436647689 31355105525529919077485767)
  ·
    refine ⟨47032658288294878616228651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31355105525529919077485767 47032658288294878616228651)
    ·
      refine ⟨70548987432442317924342977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47032658288294878616228651 70548987432442317924342977)
      ·
        refine ⟨52911740574331738443257233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70548987432442317924342977 52911740574331738443257233)
        ·
          refine ⟨39683805430748803832442925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52911740574331738443257233 39683805430748803832442925)
          ·
            refine ⟨14881427036530801437166097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39683805430748803832442925 14881427036530801437166097)
            ·
              refine ⟨11161070277398101077874573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14881427036530801437166097 11161070277398101077874573)
              ·
                refine ⟨4185401354024287904202965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11161070277398101077874573 4185401354024287904202965)
                ·
                  refine ⟨98095344234944247754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4185401354024287904202965 98095344234944247754757)
                  ·
                    rfl

theorem cell23_1719360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_1719360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719360 prefixEnd_1719360 := by exact prefixLift 1719360
  have htrace : WordTrace (prefixWord ++ tailWord_1719360) baseStart_1719360 baseEnd_1719360 := by
    simpa [prefixWord, tailWord_1719360, baseEnd_1719360] using wordTrace_append hprefix tailTrace_1719360
  have hstable : (prefixWord ++ tailWord_1719360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719360).length < 2 ^ (prefixWord ++ tailWord_1719360).sum := by decide
  have hdescent : baseEnd_1719360 < baseStart_1719360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719367 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1719367 : Nat := 118140960795 + 1719367 * 2 ^ 59
def prefixEnd_1719367 : Nat := 4983230072969 + 3 ^ 40 * 1719367 * 2
def baseEnd_1719367 : Nat := 882861692479079702405281

theorem tailTrace_1719367 : CollatzResearch.WordTrace tailWord_1719367 prefixEnd_1719367 882861692479079702405281 := by
  unfold tailWord_1719367
  simp only [CollatzResearch.WordTrace]
  refine ⟨62710466362034478350476355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41806977574689652233650903 62710466362034478350476355)
  ·
    refine ⟨94065699543051717525714533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62710466362034478350476355 94065699543051717525714533)
    ·
      refine ⟨17637318664322197036071475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94065699543051717525714533 17637318664322197036071475)
      ·
        refine ⟨26455977996483295554107213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17637318664322197036071475 26455977996483295554107213)
        ·
          refine ⟨9920991748681235832790205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26455977996483295554107213 9920991748681235832790205)
          ·
            refine ⟨3720371905755463437296327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9920991748681235832790205 3720371905755463437296327)
            ·
              refine ⟨5580557858633195155944491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720371905755463437296327 5580557858633195155944491)
              ·
                refine ⟨8370836787949792733916737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580557858633195155944491 8370836787949792733916737)
                ·
                  refine ⟨6278127590962344550437553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8370836787949792733916737 6278127590962344550437553)
                  ·
                    refine ⟨4708595693221758412828165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278127590962344550437553 4708595693221758412828165)
                    ·
                      refine ⟨882861692479079702405281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4708595693221758412828165 882861692479079702405281)
                      ·
                        rfl

theorem cell23_1719367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1719367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719367 prefixEnd_1719367 := by exact prefixLift 1719367
  have htrace : WordTrace (prefixWord ++ tailWord_1719367) baseStart_1719367 baseEnd_1719367 := by
    simpa [prefixWord, tailWord_1719367, baseEnd_1719367] using wordTrace_append hprefix tailTrace_1719367
  have hstable : (prefixWord ++ tailWord_1719367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719367).length < 2 ^ (prefixWord ++ tailWord_1719367).sum := by decide
  have hdescent : baseEnd_1719367 < baseStart_1719367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719422 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1719422 : Nat := 118140960795 + 1719422 * 2 ^ 59
def prefixEnd_1719422 : Nat := 4983230072969 + 3 ^ 40 * 1719422 * 2
def baseEnd_1719422 : Nat := 882889933915076987217529

theorem tailTrace_1719422 : CollatzResearch.WordTrace tailWord_1719422 prefixEnd_1719422 882889933915076987217529 := by
  unfold tailWord_1719422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839059047104402842966065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41808314917890148495819013 7839059047104402842966065)
  ·
    refine ⟨5879294285328302132224549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7839059047104402842966065 5879294285328302132224549)
    ·
      refine ⟨1102367678499056649792103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5879294285328302132224549 1102367678499056649792103)
      ·
        refine ⟨1653551517748584974688155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102367678499056649792103 1653551517748584974688155)
        ·
          refine ⟨2480327276622877462032233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653551517748584974688155 2480327276622877462032233)
          ·
            refine ⟨1860245457467158096524175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2480327276622877462032233 1860245457467158096524175)
            ·
              refine ⟨2790368186200737144786263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860245457467158096524175 2790368186200737144786263)
              ·
                refine ⟨4185552279301105717179395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790368186200737144786263 4185552279301105717179395)
                ·
                  refine ⟨6278328418951658575769093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185552279301105717179395 6278328418951658575769093)
                  ·
                    refine ⟨1177186578553435982956705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278328418951658575769093 1177186578553435982956705)
                    ·
                      refine ⟨882889933915076987217529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177186578553435982956705 882889933915076987217529)
                      ·
                        rfl

theorem cell23_1719422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1719422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719422 prefixEnd_1719422 := by exact prefixLift 1719422
  have htrace : WordTrace (prefixWord ++ tailWord_1719422) baseStart_1719422 baseEnd_1719422 := by
    simpa [prefixWord, tailWord_1719422, baseEnd_1719422] using wordTrace_append hprefix tailTrace_1719422
  have hstable : (prefixWord ++ tailWord_1719422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719422).length < 2 ^ (prefixWord ++ tailWord_1719422).sum := by decide
  have hdescent : baseEnd_1719422 < baseStart_1719422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719440 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1719440 : Nat := 118140960795 + 1719440 * 2 ^ 59
def prefixEnd_1719440 : Nat := 4983230072969 + 3 ^ 40 * 1719440 * 2
def baseEnd_1719440 : Nat := 882899176566857916792445

theorem tailTrace_1719440 : CollatzResearch.WordTrace tailWord_1719440 prefixEnd_1719440 882899176566857916792445 := by
  unfold tailWord_1719440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31356564445385005908941887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41808752593846674545255849 31356564445385005908941887)
  ·
    refine ⟨47034846668077508863412831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31356564445385005908941887 47034846668077508863412831)
    ·
      refine ⟨70552270002116263295119247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47034846668077508863412831 70552270002116263295119247)
      ·
        refine ⟨105828405003174394942678871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70552270002116263295119247 105828405003174394942678871)
        ·
          refine ⟨158742607504761592414018307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105828405003174394942678871 158742607504761592414018307)
          ·
            refine ⟨238113911257142388621027461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158742607504761592414018307 238113911257142388621027461)
            ·
              refine ⟨44646358360714197866442649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238113911257142388621027461 44646358360714197866442649)
              ·
                refine ⟨33484768770535648399831987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44646358360714197866442649 33484768770535648399831987)
                ·
                  refine ⟨50227153155803472599747981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33484768770535648399831987 50227153155803472599747981)
                  ·
                    refine ⟨18835182433426302224905493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50227153155803472599747981 18835182433426302224905493)
                    ·
                      refine ⟨882899176566857916792445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18835182433426302224905493 882899176566857916792445)
                      ·
                        rfl

theorem cell23_1719440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1719440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719440 prefixEnd_1719440 := by exact prefixLift 1719440
  have htrace : WordTrace (prefixWord ++ tailWord_1719440) baseStart_1719440 baseEnd_1719440 := by
    simpa [prefixWord, tailWord_1719440, baseEnd_1719440] using wordTrace_append hprefix tailTrace_1719440
  have hstable : (prefixWord ++ tailWord_1719440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719440).length < 2 ^ (prefixWord ++ tailWord_1719440).sum := by decide
  have hdescent : baseEnd_1719440 < baseStart_1719440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719484 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 6]
def baseStart_1719484 : Nat := 118140960795 + 1719484 * 2 ^ 59
def prefixEnd_1719484 : Nat := 4983230072969 + 3 ^ 40 * 1719484 * 2
def baseEnd_1719484 : Nat := 98102418857295082738027

theorem tailTrace_1719484 : CollatzResearch.WordTrace tailWord_1719484 prefixEnd_1719484 98102418857295082738027 := by
  unfold tailWord_1719484
  simp only [CollatzResearch.WordTrace]
  refine ⟨31357366851305303666242753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41809822468407071554990337 31357366851305303666242753)
  ·
    refine ⟨23518025138478977749682065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31357366851305303666242753 23518025138478977749682065)
    ·
      refine ⟨17638518853859233312261549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23518025138478977749682065 17638518853859233312261549)
      ·
        refine ⟨6614444570197212492098081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17638518853859233312261549 6614444570197212492098081)
        ·
          refine ⟨4960833427647909369073561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6614444570197212492098081 4960833427647909369073561)
          ·
            refine ⟨3720625070735932026805171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960833427647909369073561 3720625070735932026805171)
            ·
              refine ⟨5580937606103898040207757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720625070735932026805171 5580937606103898040207757)
              ·
                refine ⟨2092851602288961765077909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5580937606103898040207757 2092851602288961765077909)
                ·
                  refine ⟨98102418857295082738027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2092851602288961765077909 98102418857295082738027)
                  ·
                    rfl

theorem cell23_1719484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_1719484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719484 prefixEnd_1719484 := by exact prefixLift 1719484
  have htrace : WordTrace (prefixWord ++ tailWord_1719484) baseStart_1719484 baseEnd_1719484 := by
    simpa [prefixWord, tailWord_1719484, baseEnd_1719484] using wordTrace_append hprefix tailTrace_1719484
  have hstable : (prefixWord ++ tailWord_1719484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719484).length < 2 ^ (prefixWord ++ tailWord_1719484).sum := by decide
  have hdescent : baseEnd_1719484 < baseStart_1719484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719521 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_1719521 : Nat := 118140960795 + 1719521 * 2 ^ 59
def prefixEnd_1719521 : Nat := 4983230072969 + 3 ^ 40 * 1719521 * 2
def baseEnd_1719521 : Nat := 882940768499872099879573

theorem tailTrace_1719521 : CollatzResearch.WordTrace tailWord_1719521 prefixEnd_1719521 882940768499872099879573 := by
  unfold tailWord_1719521
  simp only [CollatzResearch.WordTrace]
  refine ⟨62716083203476562651582417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41810722135651041767721611 62716083203476562651582417)
  ·
    refine ⟨47037062402607421988686813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62716083203476562651582417 47037062402607421988686813)
    ·
      refine ⟨17638898400977783245757555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47037062402607421988686813 17638898400977783245757555)
      ·
        refine ⟨26458347601466674868636333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17638898400977783245757555 26458347601466674868636333)
        ·
          refine ⟨9921880350550003075738625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26458347601466674868636333 9921880350550003075738625)
          ·
            refine ⟨7441410262912502306803969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9921880350550003075738625 7441410262912502306803969)
            ·
              refine ⟨5581057697184376730102977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7441410262912502306803969 5581057697184376730102977)
              ·
                refine ⟨4185793272888282547577233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581057697184376730102977 4185793272888282547577233)
                ·
                  refine ⟨3139344954666211910682925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4185793272888282547577233 3139344954666211910682925)
                  ·
                    refine ⟨1177254357999829466506097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139344954666211910682925 1177254357999829466506097)
                    ·
                      refine ⟨882940768499872099879573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177254357999829466506097 882940768499872099879573)
                      ·
                        rfl

theorem cell23_1719521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_1719521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719521 prefixEnd_1719521 := by exact prefixLift 1719521
  have htrace : WordTrace (prefixWord ++ tailWord_1719521) baseStart_1719521 baseEnd_1719521 := by
    simpa [prefixWord, tailWord_1719521, baseEnd_1719521] using wordTrace_append hprefix tailTrace_1719521
  have hstable : (prefixWord ++ tailWord_1719521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719521).length < 2 ^ (prefixWord ++ tailWord_1719521).sum := by decide
  have hdescent : baseEnd_1719521 < baseStart_1719521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719528 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1719528 : Nat := 118140960795 + 1719528 * 2 ^ 59
def prefixEnd_1719528 : Nat := 4983230072969 + 3 ^ 40 * 1719528 * 2
def baseEnd_1719528 : Nat := 882944362864453572492041

theorem tailTrace_1719528 : CollatzResearch.WordTrace tailWord_1719528 prefixEnd_1719528 882944362864453572492041 := by
  unfold tailWord_1719528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358169257225601423543619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41810892342967468564724825 31358169257225601423543619)
  ·
    refine ⟨47037253885838402135315429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31358169257225601423543619 47037253885838402135315429)
    ·
      refine ⟨8819485103594700400371643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47037253885838402135315429 8819485103594700400371643)
      ·
        refine ⟨13229227655392050600557465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8819485103594700400371643 13229227655392050600557465)
        ·
          refine ⟨9921920741544037950418099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13229227655392050600557465 9921920741544037950418099)
          ·
            refine ⟨14882881112316056925627149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921920741544037950418099 14882881112316056925627149)
            ·
              refine ⟨5581080417118521347110181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14882881112316056925627149 5581080417118521347110181)
              ·
                refine ⟨1046452578209722752583159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5581080417118521347110181 1046452578209722752583159)
                ·
                  refine ⟨1569678867314584128874739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046452578209722752583159 1569678867314584128874739)
                  ·
                    refine ⟨2354518300971876193312109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1569678867314584128874739 2354518300971876193312109)
                    ·
                      refine ⟨882944362864453572492041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354518300971876193312109 882944362864453572492041)
                      ·
                        rfl

theorem cell23_1719528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1719528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719528 prefixEnd_1719528 := by exact prefixLift 1719528
  have htrace : WordTrace (prefixWord ++ tailWord_1719528) baseStart_1719528 baseEnd_1719528 := by
    simpa [prefixWord, tailWord_1719528, baseEnd_1719528] using wordTrace_append hprefix tailTrace_1719528
  have hstable : (prefixWord ++ tailWord_1719528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719528).length < 2 ^ (prefixWord ++ tailWord_1719528).sum := by decide
  have hdescent : baseEnd_1719528 < baseStart_1719528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719534 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1719534 : Nat := 118140960795 + 1719534 * 2 ^ 59
def prefixEnd_1719534 : Nat := 4983230072969 + 3 ^ 40 * 1719534 * 2
def baseEnd_1719534 : Nat := 882947443748380549017013

theorem tailTrace_1719534 : CollatzResearch.WordTrace tailWord_1719534 prefixEnd_1719534 882947443748380549017013 := by
  unfold tailWord_1719534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839569669053683233975707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41811038234952977247870437 7839569669053683233975707)
  ·
    refine ⟨11759354503580524850963561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7839569669053683233975707 11759354503580524850963561)
    ·
      refine ⟨8819515877685393638222671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11759354503580524850963561 8819515877685393638222671)
      ·
        refine ⟨13229273816528090457334007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8819515877685393638222671 13229273816528090457334007)
        ·
          refine ⟨19843910724792135686001011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13229273816528090457334007 19843910724792135686001011)
          ·
            refine ⟨29765866087188203529001517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843910724792135686001011 29765866087188203529001517)
            ·
              refine ⟨11162199782695576323375569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29765866087188203529001517 11162199782695576323375569)
              ·
                refine ⟨8371649837021682242531677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11162199782695576323375569 8371649837021682242531677)
                ·
                  refine ⟨3139368688883130840949379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8371649837021682242531677 3139368688883130840949379)
                  ·
                    refine ⟨4709053033324696261424069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3139368688883130840949379 4709053033324696261424069)
                    ·
                      refine ⟨882947443748380549017013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4709053033324696261424069 882947443748380549017013)
                      ·
                        rfl

theorem cell23_1719534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1719534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719534 prefixEnd_1719534 := by exact prefixLift 1719534
  have htrace : WordTrace (prefixWord ++ tailWord_1719534) baseStart_1719534 baseEnd_1719534 := by
    simpa [prefixWord, tailWord_1719534, baseEnd_1719534] using wordTrace_append hprefix tailTrace_1719534
  have hstable : (prefixWord ++ tailWord_1719534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719534).length < 2 ^ (prefixWord ++ tailWord_1719534).sum := by decide
  have hdescent : baseEnd_1719534 < baseStart_1719534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719537 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1719537 : Nat := 118140960795 + 1719537 * 2 ^ 59
def prefixEnd_1719537 : Nat := 4983230072969 + 3 ^ 40 * 1719537 * 2
def baseEnd_1719537 : Nat := 882948984190344037279499

theorem tailTrace_1719537 : CollatzResearch.WordTrace tailWord_1719537 prefixEnd_1719537 882948984190344037279499 := by
  unfold tailWord_1719537
  simp only [CollatzResearch.WordTrace]
  refine ⟨62716666771418597384164865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41811111180945731589443243 62716666771418597384164865)
  ·
    refine ⟨47037500078563948038123649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62716666771418597384164865 47037500078563948038123649)
    ·
      refine ⟨35278125058922961028592737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47037500078563948038123649 35278125058922961028592737)
      ·
        refine ⟨26458593794192220771444553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35278125058922961028592737 26458593794192220771444553)
        ·
          refine ⟨19843945345644165578583415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26458593794192220771444553 19843945345644165578583415)
          ·
            refine ⟨29765918018466248367875123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843945345644165578583415 29765918018466248367875123)
            ·
              refine ⟨44648877027699372551812685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29765918018466248367875123 44648877027699372551812685)
              ·
                refine ⟨16743328885387264706929757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44648877027699372551812685 16743328885387264706929757)
                ·
                  refine ⟨6278748332020224265098659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16743328885387264706929757 6278748332020224265098659)
                  ·
                    refine ⟨9418122498030336397647989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6278748332020224265098659 9418122498030336397647989)
                    ·
                      refine ⟨882948984190344037279499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9418122498030336397647989 882948984190344037279499)
                      ·
                        rfl

theorem cell23_1719537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1719537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719537 prefixEnd_1719537 := by exact prefixLift 1719537
  have htrace : WordTrace (prefixWord ++ tailWord_1719537) baseStart_1719537 baseEnd_1719537 := by
    simpa [prefixWord, tailWord_1719537, baseEnd_1719537] using wordTrace_append hprefix tailTrace_1719537
  have hstable : (prefixWord ++ tailWord_1719537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719537).length < 2 ^ (prefixWord ++ tailWord_1719537).sum := by decide
  have hdescent : baseEnd_1719537 < baseStart_1719537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719551 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 5, 2, 2]
def baseStart_1719551 : Nat := 118140960795 + 1719551 * 2 ^ 59
def prefixEnd_1719551 : Nat := 4983230072969 + 3 ^ 40 * 1719551 * 2
def baseEnd_1719551 : Nat := 882956172919506982504435

theorem tailTrace_1719551 : CollatzResearch.WordTrace tailWord_1719551 prefixEnd_1719551 882956172919506982504435 := by
  unfold tailWord_1719551
  simp only [CollatzResearch.WordTrace]
  refine ⟨62717177393367877775174507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41811451595578585183449671 62717177393367877775174507)
  ·
    refine ⟨94075766090051816662761761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62717177393367877775174507 94075766090051816662761761)
    ·
      refine ⟨70556824567538862497071321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94075766090051816662761761 70556824567538862497071321)
      ·
        refine ⟨52917618425654146872803491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70556824567538862497071321 52917618425654146872803491)
        ·
          refine ⟨79376427638481220309205237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52917618425654146872803491 79376427638481220309205237)
          ·
            refine ⟨7441540091107614403987991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79376427638481220309205237 7441540091107614403987991)
            ·
              refine ⟨11162310136661421605981987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441540091107614403987991 11162310136661421605981987)
              ·
                refine ⟨16743465204992132408972981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11162310136661421605981987 16743465204992132408972981)
                ·
                  refine ⟨1569699862968012413341217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16743465204992132408972981 1569699862968012413341217)
                  ·
                    refine ⟨1177274897226009310005913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569699862968012413341217 1177274897226009310005913)
                    ·
                      refine ⟨882956172919506982504435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177274897226009310005913 882956172919506982504435)
                      ·
                        rfl

theorem cell23_1719551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_1719551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719551 prefixEnd_1719551 := by exact prefixLift 1719551
  have htrace : WordTrace (prefixWord ++ tailWord_1719551) baseStart_1719551 baseEnd_1719551 := by
    simpa [prefixWord, tailWord_1719551, baseEnd_1719551] using wordTrace_append hprefix tailTrace_1719551
  have hstable : (prefixWord ++ tailWord_1719551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719551).length < 2 ^ (prefixWord ++ tailWord_1719551).sum := by decide
  have hdescent : baseEnd_1719551 < baseStart_1719551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719564 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1719564 : Nat := 118140960795 + 1719564 * 2 ^ 59
def prefixEnd_1719564 : Nat := 4983230072969 + 3 ^ 40 * 1719564 * 2
def baseEnd_1719564 : Nat := 882962848168015431641875

theorem tailTrace_1719564 : CollatzResearch.WordTrace tailWord_1719564 prefixEnd_1719564 882962848168015431641875 := by
  unfold tailWord_1719564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358825771160390497698873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41811767694880520663598497 31358825771160390497698873)
  ·
    refine ⟨23519119328370292873274155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31358825771160390497698873 23519119328370292873274155)
    ·
      refine ⟨35278678992555439309911233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23519119328370292873274155 35278678992555439309911233)
      ·
        refine ⟨26459009244416579482433425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35278678992555439309911233 26459009244416579482433425)
        ·
          refine ⟨19844256933312434611825069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26459009244416579482433425 19844256933312434611825069)
          ·
            refine ⟨7441596349992162979434401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19844256933312434611825069 7441596349992162979434401)
            ·
              refine ⟨5581197262494122234575801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7441596349992162979434401 5581197262494122234575801)
              ·
                refine ⟨4185897946870591675931851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581197262494122234575801 4185897946870591675931851)
                ·
                  refine ⟨6278846920305887513897777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185897946870591675931851 6278846920305887513897777)
                  ·
                    refine ⟨4709135190229415635423333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6278846920305887513897777 4709135190229415635423333)
                    ·
                      refine ⟨882962848168015431641875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4709135190229415635423333 882962848168015431641875)
                      ·
                        rfl

theorem cell23_1719564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1719564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719564 prefixEnd_1719564 := by exact prefixLift 1719564
  have htrace : WordTrace (prefixWord ++ tailWord_1719564) baseStart_1719564 baseEnd_1719564 := by
    simpa [prefixWord, tailWord_1719564, baseEnd_1719564] using wordTrace_append hprefix tailTrace_1719564
  have hstable : (prefixWord ++ tailWord_1719564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719564).length < 2 ^ (prefixWord ++ tailWord_1719564).sum := by decide
  have hdescent : baseEnd_1719564 < baseStart_1719564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719578 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_1719578 : Nat := 118140960795 + 1719578 * 2 ^ 59
def prefixEnd_1719578 : Nat := 4983230072969 + 3 ^ 40 * 1719578 * 2
def baseEnd_1719578 : Nat := 294323345632392792288937

theorem tailTrace_1719578 : CollatzResearch.WordTrace tailWord_1719578 prefixEnd_1719578 294323345632392792288937 := by
  unfold tailWord_1719578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679540541067515346601847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41812108109513374257604925 15679540541067515346601847)
  ·
    refine ⟨23519310811601273019902771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15679540541067515346601847 23519310811601273019902771)
    ·
      refine ⟨35278966217401909529854157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23519310811601273019902771 35278966217401909529854157)
      ·
        refine ⟨13229612331525716073695309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35278966217401909529854157 13229612331525716073695309)
        ·
          refine ⟨4961104624322143527635741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13229612331525716073695309 4961104624322143527635741)
          ·
            refine ⟨1860414234120803822863403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4961104624322143527635741 1860414234120803822863403)
            ·
              refine ⟨2790621351181205734295105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860414234120803822863403 2790621351181205734295105)
              ·
                refine ⟨2092966013385904300721329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790621351181205734295105 2092966013385904300721329)
                ·
                  refine ⟨1569724510039428225540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2092966013385904300721329 1569724510039428225540997)
                  ·
                    refine ⟨294323345632392792288937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1569724510039428225540997 294323345632392792288937)
                    ·
                      rfl

theorem cell23_1719578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_1719578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719578 prefixEnd_1719578 := by exact prefixLift 1719578
  have htrace : WordTrace (prefixWord ++ tailWord_1719578) baseStart_1719578 baseEnd_1719578 := by
    simpa [prefixWord, tailWord_1719578, baseEnd_1719578] using wordTrace_append hprefix tailTrace_1719578
  have hstable : (prefixWord ++ tailWord_1719578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719578).length < 2 ^ (prefixWord ++ tailWord_1719578).sum := by decide
  have hdescent : baseEnd_1719578 < baseStart_1719578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719601 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1719601 : Nat := 118140960795 + 1719601 * 2 ^ 59
def prefixEnd_1719601 : Nat := 4983230072969 + 3 ^ 40 * 1719601 * 2
def baseEnd_1719601 : Nat := 882981846952231786879205

theorem tailTrace_1719601 : CollatzResearch.WordTrace tailWord_1719601 prefixEnd_1719601 882981846952231786879205 := by
  unfold tailWord_1719601
  simp only [CollatzResearch.WordTrace]
  refine ⟨62719001043186736314494657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41812667362124490876329771 62719001043186736314494657)
  ·
    refine ⟨47039250782390052235870993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62719001043186736314494657 47039250782390052235870993)
    ·
      refine ⟨35279438086792539176903245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47039250782390052235870993 35279438086792539176903245)
      ·
        refine ⟨13229789282547202191338717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35279438086792539176903245 13229789282547202191338717)
        ·
          refine ⟨4961170980955200821752019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13229789282547202191338717 4961170980955200821752019)
          ·
            refine ⟨7441756471432801232628029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961170980955200821752019 7441756471432801232628029)
            ·
              refine ⟨2790658676787300462235511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7441756471432801232628029 2790658676787300462235511)
              ·
                refine ⟨4185988015180950693353267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790658676787300462235511 4185988015180950693353267)
                ·
                  refine ⟨6278982022771426040029901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185988015180950693353267 6278982022771426040029901)
                  ·
                    refine ⟨2354618258539284765011213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6278982022771426040029901 2354618258539284765011213)
                    ·
                      refine ⟨882981846952231786879205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354618258539284765011213 882981846952231786879205)
                      ·
                        rfl

theorem cell23_1719601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1719601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719601 prefixEnd_1719601 := by exact prefixLift 1719601
  have htrace : WordTrace (prefixWord ++ tailWord_1719601) baseStart_1719601 baseEnd_1719601 := by
    simpa [prefixWord, tailWord_1719601, baseEnd_1719601] using wordTrace_append hprefix tailTrace_1719601
  have hstable : (prefixWord ++ tailWord_1719601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719601).length < 2 ^ (prefixWord ++ tailWord_1719601).sum := by decide
  have hdescent : baseEnd_1719601 < baseStart_1719601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719614 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1719614 : Nat := 118140960795 + 1719614 * 2 ^ 59
def prefixEnd_1719614 : Nat := 4983230072969 + 3 ^ 40 * 1719614 * 2
def baseEnd_1719614 : Nat := 882988522200740236016645

theorem tailTrace_1719614 : CollatzResearch.WordTrace tailWord_1719614 prefixEnd_1719614 882988522200740236016645 := by
  unfold tailWord_1719614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839934399017454941839737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41812983461426426356478597 7839934399017454941839737)
  ·
    refine ⟨5879950799263091206379803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7839934399017454941839737 5879950799263091206379803)
    ·
      refine ⟨8819926198894636809569705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879950799263091206379803 8819926198894636809569705)
      ·
        refine ⟨6614944649170977607177279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8819926198894636809569705 6614944649170977607177279)
        ·
          refine ⟨9922416973756466410765919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614944649170977607177279 9922416973756466410765919)
          ·
            refine ⟨14883625460634699616148879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922416973756466410765919 14883625460634699616148879)
            ·
              refine ⟨22325438190952049424223319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14883625460634699616148879 22325438190952049424223319)
              ·
                refine ⟨33488157286428074136334979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22325438190952049424223319 33488157286428074136334979)
                ·
                  refine ⟨50232235929642111204502469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33488157286428074136334979 50232235929642111204502469)
                  ·
                    refine ⟨9418544236807895850844213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50232235929642111204502469 9418544236807895850844213)
                    ·
                      refine ⟨882988522200740236016645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9418544236807895850844213 882988522200740236016645)
                      ·
                        rfl

theorem cell23_1719614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1719614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719614 prefixEnd_1719614 := by exact prefixLift 1719614
  have htrace : WordTrace (prefixWord ++ tailWord_1719614) baseStart_1719614 baseEnd_1719614 := by
    simpa [prefixWord, tailWord_1719614, baseEnd_1719614] using wordTrace_append hprefix tailTrace_1719614
  have hstable : (prefixWord ++ tailWord_1719614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719614).length < 2 ^ (prefixWord ++ tailWord_1719614).sum := by decide
  have hdescent : baseEnd_1719614 < baseStart_1719614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719628 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_1719628 : Nat := 118140960795 + 1719628 * 2 ^ 59
def prefixEnd_1719628 : Nat := 4983230072969 + 3 ^ 40 * 1719628 * 2
def baseEnd_1719628 : Nat := 882995710929903181241581

theorem tailTrace_1719628 : CollatzResearch.WordTrace tailWord_1719628 prefixEnd_1719628 882995710929903181241581 := by
  unfold tailWord_1719628
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359992907044459962863769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41813323876059279950485025 31359992907044459962863769)
  ·
    refine ⟨23519994680283344972147827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31359992907044459962863769 23519994680283344972147827)
    ·
      refine ⟨35279992020425017458221741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23519994680283344972147827 35279992020425017458221741)
      ·
        refine ⟨13229997007659381546833153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35279992020425017458221741 13229997007659381546833153)
        ·
          refine ⟨9922497755744536160124865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13229997007659381546833153 9922497755744536160124865)
          ·
            refine ⟨7441873316808402120093649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9922497755744536160124865 7441873316808402120093649)
            ·
              refine ⟨5581404987606301590070237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7441873316808402120093649 5581404987606301590070237)
              ·
                refine ⟨2093026870352363096276339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5581404987606301590070237 2093026870352363096276339)
                ·
                  refine ⟨3139540305528544644414509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093026870352363096276339 3139540305528544644414509)
                  ·
                    refine ⟨1177327614573204241655441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139540305528544644414509 1177327614573204241655441)
                    ·
                      refine ⟨882995710929903181241581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177327614573204241655441 882995710929903181241581)
                      ·
                        rfl

theorem cell23_1719628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_1719628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719628 prefixEnd_1719628 := by exact prefixLift 1719628
  have htrace : WordTrace (prefixWord ++ tailWord_1719628) baseStart_1719628 baseEnd_1719628 := by
    simpa [prefixWord, tailWord_1719628, baseEnd_1719628] using wordTrace_append hprefix tailTrace_1719628
  have hstable : (prefixWord ++ tailWord_1719628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719628).length < 2 ^ (prefixWord ++ tailWord_1719628).sum := by decide
  have hdescent : baseEnd_1719628 < baseStart_1719628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719674 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_1719674 : Nat := 118140960795 + 1719674 * 2 ^ 59
def prefixEnd_1719674 : Nat := 4983230072969 + 3 ^ 40 * 1719674 * 2
def baseEnd_1719674 : Nat := 883019331040010001266369

theorem tailTrace_1719674 : CollatzResearch.WordTrace tailWord_1719674 prefixEnd_1719674 883019331040010001266369 := by
  unfold tailWord_1719674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680415892980567445475519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41814442381281513187934717 15680415892980567445475519)
  ·
    refine ⟨23520623839470851168213279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15680415892980567445475519 23520623839470851168213279)
    ·
      refine ⟨35280935759206276752319919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23520623839470851168213279 35280935759206276752319919)
      ·
        refine ⟨52921403638809415128479879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35280935759206276752319919 52921403638809415128479879)
        ·
          refine ⟨79382105458214122692719819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52921403638809415128479879 79382105458214122692719819)
          ·
            refine ⟨119073158187321184039079729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79382105458214122692719819 119073158187321184039079729)
            ·
              refine ⟨89304868640490888029309797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119073158187321184039079729 89304868640490888029309797)
              ·
                refine ⟨16744662870092041505495587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89304868640490888029309797 16744662870092041505495587)
                ·
                  refine ⟨25116994305138062258243381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16744662870092041505495587 25116994305138062258243381)
                  ·
                    refine ⟨2354718216106693336710317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25116994305138062258243381 2354718216106693336710317)
                    ·
                      refine ⟨883019331040010001266369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354718216106693336710317 883019331040010001266369)
                      ·
                        rfl

theorem cell23_1719674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_1719674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719674 prefixEnd_1719674 := by exact prefixLift 1719674
  have htrace : WordTrace (prefixWord ++ tailWord_1719674) baseStart_1719674 baseEnd_1719674 := by
    simpa [prefixWord, tailWord_1719674, baseEnd_1719674] using wordTrace_append hprefix tailTrace_1719674
  have hstable : (prefixWord ++ tailWord_1719674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719674).length < 2 ^ (prefixWord ++ tailWord_1719674).sum := by decide
  have hdescent : baseEnd_1719674 < baseStart_1719674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719701 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_1719701 : Nat := 118140960795 + 1719701 * 2 ^ 59
def prefixEnd_1719701 : Nat := 4983230072969 + 3 ^ 40 * 1719701 * 2
def baseEnd_1719701 : Nat := 883033195017681395628745

theorem tailTrace_1719701 : CollatzResearch.WordTrace tailWord_1719701 prefixEnd_1719701 883033195017681395628745 := by
  unfold tailWord_1719701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62722648342824453393134957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41815098895216302262089971 62722648342824453393134957)
  ·
    refine ⟨23520993128559170022425609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62722648342824453393134957 23520993128559170022425609)
    ·
      refine ⟨17640744846419377516819207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23520993128559170022425609 17640744846419377516819207)
      ·
        refine ⟨26461117269629066275228811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17640744846419377516819207 26461117269629066275228811)
        ·
          refine ⟨39691675904443599412843217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461117269629066275228811 39691675904443599412843217)
          ·
            refine ⟨29768756928332699559632413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39691675904443599412843217 29768756928332699559632413)
            ·
              refine ⟨11163283848124762334862155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29768756928332699559632413 11163283848124762334862155)
              ·
                refine ⟨16744925772187143502293233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163283848124762334862155 16744925772187143502293233)
                ·
                  refine ⟨12558694329140357626719925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16744925772187143502293233 12558694329140357626719925)
                  ·
                    refine ⟨1177377593356908527504993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12558694329140357626719925 1177377593356908527504993)
                    ·
                      refine ⟨883033195017681395628745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177377593356908527504993 883033195017681395628745)
                      ·
                        rfl

theorem cell23_1719701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_1719701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719701 prefixEnd_1719701 := by exact prefixLift 1719701
  have htrace : WordTrace (prefixWord ++ tailWord_1719701) baseStart_1719701 baseEnd_1719701 := by
    simpa [prefixWord, tailWord_1719701, baseEnd_1719701] using wordTrace_append hprefix tailTrace_1719701
  have hstable : (prefixWord ++ tailWord_1719701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719701).length < 2 ^ (prefixWord ++ tailWord_1719701).sum := by decide
  have hdescent : baseEnd_1719701 < baseStart_1719701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719741 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1719741 : Nat := 118140960795 + 1719741 * 2 ^ 59
def prefixEnd_1719741 : Nat := 4983230072969 + 3 ^ 40 * 1719741 * 2
def baseEnd_1719741 : Nat := 294351244747953746376187

theorem tailTrace_1719741 : CollatzResearch.WordTrace tailWord_1719741 prefixEnd_1719741 294351244747953746376187 := by
  unfold tailWord_1719741
  simp only [CollatzResearch.WordTrace]
  refine ⟨62724107262679540224591077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41816071508453026816394051 62724107262679540224591077)
  ·
    refine ⟨11760770111752413792110827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62724107262679540224591077 11760770111752413792110827)
    ·
      refine ⟨17641155167628620688166241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760770111752413792110827 17641155167628620688166241)
      ·
        refine ⟨13230866375721465516124681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17641155167628620688166241 13230866375721465516124681)
        ·
          refine ⟨9923149781791099137093511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13230866375721465516124681 9923149781791099137093511)
          ·
            refine ⟨14884724672686648705640267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9923149781791099137093511 14884724672686648705640267)
            ·
              refine ⟨22327087009029973058460401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14884724672686648705640267 22327087009029973058460401)
              ·
                refine ⟨16745315256772479793845301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22327087009029973058460401 16745315256772479793845301)
                ·
                  refine ⟨1569873305322419980672997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16745315256772479793845301 1569873305322419980672997)
                  ·
                    refine ⟨294351244747953746376187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1569873305322419980672997 294351244747953746376187)
                    ·
                      rfl

theorem cell23_1719741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1719741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719741 prefixEnd_1719741 := by exact prefixLift 1719741
  have htrace : WordTrace (prefixWord ++ tailWord_1719741) baseStart_1719741 baseEnd_1719741 := by
    simpa [prefixWord, tailWord_1719741, baseEnd_1719741] using wordTrace_append hprefix tailTrace_1719741
  have hstable : (prefixWord ++ tailWord_1719741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719741).length < 2 ^ (prefixWord ++ tailWord_1719741).sum := by decide
  have hdescent : baseEnd_1719741 < baseStart_1719741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719744 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1719744 : Nat := 118140960795 + 1719744 * 2 ^ 59
def prefixEnd_1719744 : Nat := 4983230072969 + 3 ^ 40 * 1719744 * 2
def baseEnd_1719744 : Nat := 883055274685824727391047

theorem tailTrace_1719744 : CollatzResearch.WordTrace tailWord_1719744 prefixEnd_1719744 883055274685824727391047 := by
  unfold tailWord_1719744
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362108340834335868475143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41816144454445781157966857 31362108340834335868475143)
  ·
    refine ⟨47043162511251503802712715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31362108340834335868475143 47043162511251503802712715)
    ·
      refine ⟨70564743766877255704069073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47043162511251503802712715 70564743766877255704069073)
      ·
        refine ⟨52923557825157941778051805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70564743766877255704069073 52923557825157941778051805)
        ·
          refine ⟨19846334184434228166769427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52923557825157941778051805 19846334184434228166769427)
          ·
            refine ⟨29769501276651342250154141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19846334184434228166769427 29769501276651342250154141)
            ·
              refine ⟨11163562978744253343807803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29769501276651342250154141 11163562978744253343807803)
              ·
                refine ⟨16745344468116380015711705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163562978744253343807803 16745344468116380015711705)
                ·
                  refine ⟨12559008351087285011783779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16745344468116380015711705 12559008351087285011783779)
                  ·
                    refine ⟨18838512526630927517675669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12559008351087285011783779 18838512526630927517675669)
                    ·
                      refine ⟨883055274685824727391047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18838512526630927517675669 883055274685824727391047)
                      ·
                        rfl

theorem cell23_1719744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1719744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719744 prefixEnd_1719744 := by exact prefixLift 1719744
  have htrace : WordTrace (prefixWord ++ tailWord_1719744) baseStart_1719744 baseEnd_1719744 := by
    simpa [prefixWord, tailWord_1719744, baseEnd_1719744] using wordTrace_append hprefix tailTrace_1719744
  have hstable : (prefixWord ++ tailWord_1719744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719744).length < 2 ^ (prefixWord ++ tailWord_1719744).sum := by decide
  have hdescent : baseEnd_1719744 < baseStart_1719744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719751 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1719751 : Nat := 118140960795 + 1719751 * 2 ^ 59
def prefixEnd_1719751 : Nat := 4983230072969 + 3 ^ 40 * 1719751 * 2
def baseEnd_1719751 : Nat := 883058869050406200003515

theorem tailTrace_1719751 : CollatzResearch.WordTrace tailWord_1719751 prefixEnd_1719751 883058869050406200003515 := by
  unfold tailWord_1719751
  simp only [CollatzResearch.WordTrace]
  refine ⟨62724471992643311932455107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41816314661762207954970071 62724471992643311932455107)
  ·
    refine ⟨94086707988964967898682661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62724471992643311932455107 94086707988964967898682661)
    ·
      refine ⟨17641257747930931481002999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94086707988964967898682661 17641257747930931481002999)
      ·
        refine ⟨26461886621896397221504499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17641257747930931481002999 26461886621896397221504499)
        ·
          refine ⟨39692829932844595832256749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461886621896397221504499 39692829932844595832256749)
          ·
            refine ⟨14884811224816723437096281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39692829932844595832256749 14884811224816723437096281)
            ·
              refine ⟨11163608418612542577822211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14884811224816723437096281 11163608418612542577822211)
              ·
                refine ⟨16745412627918813866733317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163608418612542577822211 16745412627918813866733317)
                ·
                  refine ⟨3139764867734777600012497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16745412627918813866733317 3139764867734777600012497)
                  ·
                    refine ⟨2354823650801083200009373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3139764867734777600012497 2354823650801083200009373)
                    ·
                      refine ⟨883058869050406200003515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354823650801083200009373 883058869050406200003515)
                      ·
                        rfl

theorem cell23_1719751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1719751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719751 prefixEnd_1719751 := by exact prefixLift 1719751
  have htrace : WordTrace (prefixWord ++ tailWord_1719751) baseStart_1719751 baseEnd_1719751 := by
    simpa [prefixWord, tailWord_1719751, baseEnd_1719751] using wordTrace_append hprefix tailTrace_1719751
  have hstable : (prefixWord ++ tailWord_1719751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719751).length < 2 ^ (prefixWord ++ tailWord_1719751).sum := by decide
  have hdescent : baseEnd_1719751 < baseStart_1719751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719815 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1719815 : Nat := 118140960795 + 1719815 * 2 ^ 59
def prefixEnd_1719815 : Nat := 4983230072969 + 3 ^ 40 * 1719815 * 2
def baseEnd_1719815 : Nat := 883091731812293949603221

theorem tailTrace_1719815 : CollatzResearch.WordTrace tailWord_1719815 prefixEnd_1719815 883091731812293949603221 := by
  unfold tailWord_1719815
  simp only [CollatzResearch.WordTrace]
  refine ⟨62726806264411450862784899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41817870842940967241856599 62726806264411450862784899)
  ·
    refine ⟨94090209396617176294177349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62726806264411450862784899 94090209396617176294177349)
    ·
      refine ⟨17641914261865720555158253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94090209396617176294177349 17641914261865720555158253)
      ·
        refine ⟨6615717848199645208184345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17641914261865720555158253 6615717848199645208184345)
        ·
          refine ⟨4961788386149733906138259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615717848199645208184345 4961788386149733906138259)
          ·
            refine ⟨7442682579224600859207389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961788386149733906138259 7442682579224600859207389)
            ·
              refine ⟨2791005967209225322202771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7442682579224600859207389 2791005967209225322202771)
              ·
                refine ⟨4186508950813837983304157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791005967209225322202771 4186508950813837983304157)
                ·
                  refine ⟨1569940856555189243739059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4186508950813837983304157 1569940856555189243739059)
                  ·
                    refine ⟨2354911284832783865608589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1569940856555189243739059 2354911284832783865608589)
                    ·
                      refine ⟨883091731812293949603221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2354911284832783865608589 883091731812293949603221)
                      ·
                        rfl

theorem cell23_1719815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1719815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719815 prefixEnd_1719815 := by exact prefixLift 1719815
  have htrace : WordTrace (prefixWord ++ tailWord_1719815) baseStart_1719815 baseEnd_1719815 := by
    simpa [prefixWord, tailWord_1719815, baseEnd_1719815] using wordTrace_append hprefix tailTrace_1719815
  have hstable : (prefixWord ++ tailWord_1719815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719815).length < 2 ^ (prefixWord ++ tailWord_1719815).sum := by decide
  have hdescent : baseEnd_1719815 < baseStart_1719815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719822 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_1719822 : Nat := 118140960795 + 1719822 * 2 ^ 59
def prefixEnd_1719822 : Nat := 4983230072969 + 3 ^ 40 * 1719822 * 2
def baseEnd_1719822 : Nat := 98121702908541713579521

theorem tailTrace_1719822 : CollatzResearch.WordTrace tailWord_1719822 prefixEnd_1719822 98121702908541713579521 := by
  unfold tailWord_1719822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7840882696923261382286215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41818041050257394038859813 7840882696923261382286215)
  ·
    refine ⟨11761324045384892073429323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7840882696923261382286215 11761324045384892073429323)
    ·
      refine ⟨17641986068077338110143985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761324045384892073429323 17641986068077338110143985)
      ·
        refine ⟨13231489551058003582607989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17641986068077338110143985 13231489551058003582607989)
        ·
          refine ⟨1240452145411687835869499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13231489551058003582607989 1240452145411687835869499)
          ·
            refine ⟨1860678218117531753804249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240452145411687835869499 1860678218117531753804249)
            ·
              refine ⟨1395508663588148815353187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860678218117531753804249 1395508663588148815353187)
              ·
                refine ⟨2093262995382223223029781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395508663588148815353187 2093262995382223223029781)
                ·
                  refine ⟨98121702908541713579521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2093262995382223223029781 98121702908541713579521)
                  ·
                    rfl

theorem cell23_1719822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_1719822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719822 prefixEnd_1719822 := by exact prefixLift 1719822
  have htrace : WordTrace (prefixWord ++ tailWord_1719822) baseStart_1719822 baseEnd_1719822 := by
    simpa [prefixWord, tailWord_1719822, baseEnd_1719822] using wordTrace_append hprefix tailTrace_1719822
  have hstable : (prefixWord ++ tailWord_1719822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719822).length < 2 ^ (prefixWord ++ tailWord_1719822).sum := by decide
  have hdescent : baseEnd_1719822 < baseStart_1719822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719865 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_1719865 : Nat := 118140960795 + 1719865 * 2 ^ 59
def prefixEnd_1719865 : Nat := 4983230072969 + 3 ^ 40 * 1719865 * 2
def baseEnd_1719865 : Nat := 294372468615006251325997

theorem tailTrace_1719865 : CollatzResearch.WordTrace tailWord_1719865 prefixEnd_1719865 294372468615006251325997 := by
  unfold tailWord_1719865
  simp only [CollatzResearch.WordTrace]
  refine ⟨62728629914230309402105049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41819086609486872934736699 62728629914230309402105049)
  ·
    refine ⟨47046472435672732051578787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62728629914230309402105049 47046472435672732051578787)
    ·
      refine ⟨70569708653509098077368181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47046472435672732051578787 70569708653509098077368181)
      ·
        refine ⟨6615910186266477944753267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70569708653509098077368181 6615910186266477944753267)
        ·
          refine ⟨9923865279399716917129901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615910186266477944753267 9923865279399716917129901)
          ·
            refine ⟨3721449479774893843923713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9923865279399716917129901 3721449479774893843923713)
            ·
              refine ⟨2791087109831170382942785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721449479774893843923713 2791087109831170382942785)
              ·
                refine ⟨2093315332373377787207089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791087109831170382942785 2093315332373377787207089)
                ·
                  refine ⟨1569986499280033340405317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093315332373377787207089 1569986499280033340405317)
                  ·
                    refine ⟨294372468615006251325997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1569986499280033340405317 294372468615006251325997)
                    ·
                      rfl

theorem cell23_1719865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_1719865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719865 prefixEnd_1719865 := by exact prefixLift 1719865
  have htrace : WordTrace (prefixWord ++ tailWord_1719865) baseStart_1719865 baseEnd_1719865 := by
    simpa [prefixWord, tailWord_1719865, baseEnd_1719865] using wordTrace_append hprefix tailTrace_1719865
  have hstable : (prefixWord ++ tailWord_1719865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719865).length < 2 ^ (prefixWord ++ tailWord_1719865).sum := by decide
  have hdescent : baseEnd_1719865 < baseStart_1719865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719888 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_1719888 : Nat := 118140960795 + 1719888 * 2 ^ 59
def prefixEnd_1719888 : Nat := 4983230072969 + 3 ^ 40 * 1719888 * 2
def baseEnd_1719888 : Nat := 883129215900072163990385

theorem tailTrace_1719888 : CollatzResearch.WordTrace tailWord_1719888 prefixEnd_1719888 883129215900072163990385 := by
  unfold tailWord_1719888
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364734396573492165096159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41819645862097989553461545 31364734396573492165096159)
  ·
    refine ⟨47047101594860238247644239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31364734396573492165096159 47047101594860238247644239)
    ·
      refine ⟨70570652392290357371466359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47047101594860238247644239 70570652392290357371466359)
      ·
        refine ⟨105855978588435536057199539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70570652392290357371466359 105855978588435536057199539)
        ·
          refine ⟨158783967882653304085799309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105855978588435536057199539 158783967882653304085799309)
          ·
            refine ⟨59543987955994989032174741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158783967882653304085799309 59543987955994989032174741)
            ·
              refine ⟨2791124435437265110883191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59543987955994989032174741 2791124435437265110883191)
              ·
                refine ⟨4186686653155897666324787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791124435437265110883191 4186686653155897666324787)
                ·
                  refine ⟨6280029979733846499487181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186686653155897666324787 6280029979733846499487181)
                  ·
                    refine ⟨2355011242400192437307693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6280029979733846499487181 2355011242400192437307693)
                    ·
                      refine ⟨883129215900072163990385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2355011242400192437307693 883129215900072163990385)
                      ·
                        rfl

theorem cell23_1719888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_1719888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719888 prefixEnd_1719888 := by exact prefixLift 1719888
  have htrace : WordTrace (prefixWord ++ tailWord_1719888) baseStart_1719888 baseEnd_1719888 := by
    simpa [prefixWord, tailWord_1719888, baseEnd_1719888] using wordTrace_append hprefix tailTrace_1719888
  have hstable : (prefixWord ++ tailWord_1719888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719888).length < 2 ^ (prefixWord ++ tailWord_1719888).sum := by decide
  have hdescent : baseEnd_1719888 < baseStart_1719888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719922 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1719922 : Nat := 118140960795 + 1719922 * 2 ^ 59
def prefixEnd_1719922 : Nat := 4983230072969 + 3 ^ 40 * 1719922 * 2
def baseEnd_1719922 : Nat := 883146674242325030965229

theorem tailTrace_1719922 : CollatzResearch.WordTrace tailWord_1719922 prefixEnd_1719922 883146674242325030965229 := by
  unfold tailWord_1719922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682677218755952034232505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41820472583349205424620013 15682677218755952034232505)
  ·
    refine ⟨11762007914066964025674379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15682677218755952034232505 11762007914066964025674379)
    ·
      refine ⟨17643011871100446038511569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11762007914066964025674379 17643011871100446038511569)
      ·
        refine ⟨13232258903325334528883677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17643011871100446038511569 13232258903325334528883677)
        ·
          refine ⟨4962097088747000448331379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13232258903325334528883677 4962097088747000448331379)
          ·
            refine ⟨7443145633120500672497069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962097088747000448331379 7443145633120500672497069)
            ·
              refine ⟨2791179612420187752186401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7443145633120500672497069 2791179612420187752186401)
              ·
                refine ⟨2093384709315140814139801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791179612420187752186401 2093384709315140814139801)
                ·
                  refine ⟨1570038531986355610604851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093384709315140814139801 1570038531986355610604851)
                  ·
                    refine ⟨2355057797979533415907277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570038531986355610604851 2355057797979533415907277)
                    ·
                      refine ⟨883146674242325030965229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2355057797979533415907277 883146674242325030965229)
                      ·
                        rfl

theorem cell23_1719922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1719922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719922 prefixEnd_1719922 := by exact prefixLift 1719922
  have htrace : WordTrace (prefixWord ++ tailWord_1719922) baseStart_1719922 baseEnd_1719922 := by
    simpa [prefixWord, tailWord_1719922, baseEnd_1719922] using wordTrace_append hprefix tailTrace_1719922
  have hstable : (prefixWord ++ tailWord_1719922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719922).length < 2 ^ (prefixWord ++ tailWord_1719922).sum := by decide
  have hdescent : baseEnd_1719922 < baseStart_1719922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719945 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 1, 4, 2]
def baseStart_1719945 : Nat := 118140960795 + 1719945 * 2 ^ 59
def prefixEnd_1719945 : Nat := 4983230072969 + 3 ^ 40 * 1719945 * 2
def baseEnd_1719945 : Nat := 883158484297378440977623

theorem tailTrace_1719945 : CollatzResearch.WordTrace tailWord_1719945 prefixEnd_1719945 883158484297378440977623 := by
  unfold tailWord_1719945
  simp only [CollatzResearch.WordTrace]
  refine ⟨62731547753940483065017289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41821031835960322043344859 62731547753940483065017289)
  ·
    refine ⟨47048660815455362298762967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62731547753940483065017289 47048660815455362298762967)
    ·
      refine ⟨70572991223183043448144451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47048660815455362298762967 70572991223183043448144451)
      ·
        refine ⟨105859486834774565172216677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70572991223183043448144451 105859486834774565172216677)
        ·
          refine ⟨19848653781520230969790627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105859486834774565172216677 19848653781520230969790627)
          ·
            refine ⟨29772980672280346454685941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19848653781520230969790627 29772980672280346454685941)
            ·
              refine ⟨2791216938026282480126807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29772980672280346454685941 2791216938026282480126807)
              ·
                refine ⟨4186825407039423720190211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791216938026282480126807 4186825407039423720190211)
                ·
                  refine ⟨6280238110559135580285317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186825407039423720190211 6280238110559135580285317)
                  ·
                    refine ⟨1177544645729837921303497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280238110559135580285317 1177544645729837921303497)
                    ·
                      refine ⟨883158484297378440977623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177544645729837921303497 883158484297378440977623)
                      ·
                        rfl

theorem cell23_1719945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4, 2].length) (baseStart_1719945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719945 prefixEnd_1719945 := by exact prefixLift 1719945
  have htrace : WordTrace (prefixWord ++ tailWord_1719945) baseStart_1719945 baseEnd_1719945 := by
    simpa [prefixWord, tailWord_1719945, baseEnd_1719945] using wordTrace_append hprefix tailTrace_1719945
  have hstable : (prefixWord ++ tailWord_1719945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719945).length < 2 ^ (prefixWord ++ tailWord_1719945).sum := by decide
  have hdescent : baseEnd_1719945 < baseStart_1719945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719996 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1719996 : Nat := 118140960795 + 1719996 * 2 ^ 59
def prefixEnd_1719996 : Nat := 4983230072969 + 3 ^ 40 * 1719996 * 2
def baseEnd_1719996 : Nat := 883184671810757741439889

theorem tailTrace_1719996 : CollatzResearch.WordTrace tailWord_1719996 prefixEnd_1719996 883184671810757741439889 := by
  unfold tailWord_1719996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31366703938377859387561921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41822271917837145850082561 31366703938377859387561921)
  ·
    refine ⟨23525027953783394540671441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31366703938377859387561921 23525027953783394540671441)
    ·
      refine ⟨17643770965337545905503581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23525027953783394540671441 17643770965337545905503581)
      ·
        refine ⟨6616414112001579714563843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17643770965337545905503581 6616414112001579714563843)
        ·
          refine ⟨9924621168002369571845765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6616414112001579714563843 9924621168002369571845765)
          ·
            refine ⟨1860866469000444294721081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9924621168002369571845765 1860866469000444294721081)
            ·
              refine ⟨1395649851750333221040811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860866469000444294721081 1395649851750333221040811)
              ·
                refine ⟨2093474777625499831561217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395649851750333221040811 2093474777625499831561217)
                ·
                  refine ⟨1570106083219124873670913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093474777625499831561217 1570106083219124873670913)
                  ·
                    refine ⟨1177579562414343655253185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570106083219124873670913 1177579562414343655253185)
                    ·
                      refine ⟨883184671810757741439889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177579562414343655253185 883184671810757741439889)
                      ·
                        rfl

theorem cell23_1719996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1719996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1719996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1719996 prefixEnd_1719996 := by exact prefixLift 1719996
  have htrace : WordTrace (prefixWord ++ tailWord_1719996) baseStart_1719996 baseEnd_1719996 := by
    simpa [prefixWord, tailWord_1719996, baseEnd_1719996] using wordTrace_append hprefix tailTrace_1719996
  have hstable : (prefixWord ++ tailWord_1719996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719996).length < 2 ^ (prefixWord ++ tailWord_1719996).sum := by decide
  have hdescent : baseEnd_1719996 < baseStart_1719996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720011 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 8]
def baseStart_1720011 : Nat := 118140960795 + 1720011 * 2 ^ 59
def prefixEnd_1720011 : Nat := 4983230072969 + 3 ^ 40 * 1720011 * 2
def baseEnd_1720011 : Nat := 294397458006858394250773

theorem tailTrace_1720011 : CollatzResearch.WordTrace tailWord_1720011 prefixEnd_1720011 294397458006858394250773 := by
  unfold tailWord_1720011
  simp only [CollatzResearch.WordTrace]
  refine ⟨62733954971701376336919887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41822636647800917557946591 62733954971701376336919887)
  ·
    refine ⟨94100932457552064505379831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62733954971701376336919887 94100932457552064505379831)
    ·
      refine ⟨141151398686328096758069747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94100932457552064505379831 141151398686328096758069747)
      ·
        refine ⟨211727098029492145137104621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141151398686328096758069747 211727098029492145137104621)
        ·
          refine ⟨79397661761059554426414233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211727098029492145137104621 79397661761059554426414233)
          ·
            refine ⟨59548246320794665819810675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79397661761059554426414233 59548246320794665819810675)
            ·
              refine ⟨89322369481191998729716013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59548246320794665819810675 89322369481191998729716013)
              ·
                refine ⟨33495888555446999523643505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89322369481191998729716013 33495888555446999523643505)
                ·
                  refine ⟨25121916416585249642732629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33495888555446999523643505 25121916416585249642732629)
                  ·
                    refine ⟨294397458006858394250773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25121916416585249642732629 294397458006858394250773)
                    ·
                      rfl

theorem cell23_1720011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_1720011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720011 prefixEnd_1720011 := by exact prefixLift 1720011
  have htrace : WordTrace (prefixWord ++ tailWord_1720011) baseStart_1720011 baseEnd_1720011 := by
    simpa [prefixWord, tailWord_1720011, baseEnd_1720011] using wordTrace_append hprefix tailTrace_1720011
  have hstable : (prefixWord ++ tailWord_1720011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720011).length < 2 ^ (prefixWord ++ tailWord_1720011).sum := by decide
  have hdescent : baseEnd_1720011 < baseStart_1720011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720070 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1720070 : Nat := 118140960795 + 1720070 * 2 ^ 59
def prefixEnd_1720070 : Nat := 4983230072969 + 3 ^ 40 * 1720070 * 2
def baseEnd_1720070 : Nat := 98135852153243383546061

theorem tailTrace_1720070 : CollatzResearch.WordTrace tailWord_1720070 prefixEnd_1720070 98135852153243383546061 := by
  unfold tailWord_1720070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960503339952738419166177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41824071252325086275545109 1960503339952738419166177)
  ·
    refine ⟨1470377504964553814374633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1960503339952738419166177 1470377504964553814374633)
    ·
      refine ⟨1102783128723415360780975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1470377504964553814374633 1102783128723415360780975)
      ·
        refine ⟨1654174693085123041171463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102783128723415360780975 1654174693085123041171463)
        ·
          refine ⟨2481262039627684561757195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654174693085123041171463 2481262039627684561757195)
          ·
            refine ⟨3721893059441526842635793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481262039627684561757195 3721893059441526842635793)
            ·
              refine ⟨2791419794581145131976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721893059441526842635793 2791419794581145131976845)
              ·
                refine ⟨1046782422967929424491317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791419794581145131976845 1046782422967929424491317)
                ·
                  refine ⟨98135852153243383546061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046782422967929424491317 98135852153243383546061)
                  ·
                    rfl

theorem cell23_1720070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1720070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720070 prefixEnd_1720070 := by exact prefixLift 1720070
  have htrace : WordTrace (prefixWord ++ tailWord_1720070) baseStart_1720070 baseEnd_1720070 := by
    simpa [prefixWord, tailWord_1720070, baseEnd_1720070] using wordTrace_append hprefix tailTrace_1720070
  have hstable : (prefixWord ++ tailWord_1720070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720070).length < 2 ^ (prefixWord ++ tailWord_1720070).sum := by decide
  have hdescent : baseEnd_1720070 < baseStart_1720070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720122 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_1720122 : Nat := 118140960795 + 1720122 * 2 ^ 59
def prefixEnd_1720122 : Nat := 4983230072969 + 3 ^ 40 * 1720122 * 2
def baseEnd_1720122 : Nat := 294416456791074749488103

theorem tailTrace_1720122 : CollatzResearch.WordTrace tailWord_1720122 prefixEnd_1720122 294416456791074749488103 := by
  unfold tailWord_1720122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15684500868574810573552655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41825335649532828196140413 15684500868574810573552655)
  ·
    refine ⟨23526751302862215860328983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15684500868574810573552655 23526751302862215860328983)
    ·
      refine ⟨35290126954293323790493475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23526751302862215860328983 35290126954293323790493475)
      ·
        refine ⟨52935190431439985685740213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35290126954293323790493475 52935190431439985685740213)
        ·
          refine ⟨4962674102947498658038145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52935190431439985685740213 4962674102947498658038145)
          ·
            refine ⟨3722005577210623993528609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4962674102947498658038145 3722005577210623993528609)
            ·
              refine ⟨2791504182907967995146457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722005577210623993528609 2791504182907967995146457)
              ·
                refine ⟨2093628137180975996359843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791504182907967995146457 2093628137180975996359843)
                ·
                  refine ⟨3140442205771463994539765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093628137180975996359843 3140442205771463994539765)
                  ·
                    refine ⟨294416456791074749488103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3140442205771463994539765 294416456791074749488103)
                    ·
                      rfl

theorem cell23_1720122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_1720122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720122 prefixEnd_1720122 := by exact prefixLift 1720122
  have htrace : WordTrace (prefixWord ++ tailWord_1720122) baseStart_1720122 baseEnd_1720122 := by
    simpa [prefixWord, tailWord_1720122, baseEnd_1720122] using wordTrace_append hprefix tailTrace_1720122
  have hstable : (prefixWord ++ tailWord_1720122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720122).length < 2 ^ (prefixWord ++ tailWord_1720122).sum := by decide
  have hdescent : baseEnd_1720122 < baseStart_1720122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720135 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 4, 4]
def baseStart_1720135 : Nat := 118140960795 + 1720135 * 2 ^ 59
def prefixEnd_1720135 : Nat := 4983230072969 + 3 ^ 40 * 1720135 * 2
def baseEnd_1720135 : Nat := 294418681873910899200583

theorem tailTrace_1720135 : CollatzResearch.WordTrace tailWord_1720135 prefixEnd_1720135 294418681873910899200583 := by
  unfold tailWord_1720135
  simp only [CollatzResearch.WordTrace]
  refine ⟨62738477623252145514433859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41825651748834763676289239 62738477623252145514433859)
  ·
    refine ⟨94107716434878218271650789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62738477623252145514433859 94107716434878218271650789)
    ·
      refine ⟨17645196831539665925934523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94107716434878218271650789 17645196831539665925934523)
      ·
        refine ⟨26467795247309498888901785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17645196831539665925934523 26467795247309498888901785)
        ·
          refine ⟨19850846435482124166676339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26467795247309498888901785 19850846435482124166676339)
          ·
            refine ⟨29776269653223186250014509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19850846435482124166676339 29776269653223186250014509)
            ·
              refine ⟨11166101119958694843755441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29776269653223186250014509 11166101119958694843755441)
              ·
                refine ⟨8374575839969021132816581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166101119958694843755441 8374575839969021132816581)
                ·
                  refine ⟨1570232969994191462403109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8374575839969021132816581 1570232969994191462403109)
                  ·
                    refine ⟨294418681873910899200583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1570232969994191462403109 294418681873910899200583)
                    ·
                      rfl

theorem cell23_1720135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_1720135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720135 prefixEnd_1720135 := by exact prefixLift 1720135
  have htrace : WordTrace (prefixWord ++ tailWord_1720135) baseStart_1720135 baseEnd_1720135 := by
    simpa [prefixWord, tailWord_1720135, baseEnd_1720135] using wordTrace_append hprefix tailTrace_1720135
  have hstable : (prefixWord ++ tailWord_1720135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720135).length < 2 ^ (prefixWord ++ tailWord_1720135).sum := by decide
  have hdescent : baseEnd_1720135 < baseStart_1720135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720136 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_1720136 : Nat := 118140960795 + 1720136 * 2 ^ 59
def prefixEnd_1720136 : Nat := 4983230072969 + 3 ^ 40 * 1720136 * 2
def baseEnd_1720136 : Nat := 883256559102387193689245

theorem tailTrace_1720136 : CollatzResearch.WordTrace tailWord_1720136 prefixEnd_1720136 883256559102387193689245 := by
  unfold tailWord_1720136
  simp only [CollatzResearch.WordTrace]
  refine ⟨31369257048124261342610131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41825676064165681790146841 31369257048124261342610131)
  ·
    refine ⟨47053885572186392013915197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31369257048124261342610131 47053885572186392013915197)
    ·
      refine ⟨17645207089569897005218199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47053885572186392013915197 17645207089569897005218199)
      ·
        refine ⟨26467810634354845507827299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17645207089569897005218199 26467810634354845507827299)
        ·
          refine ⟨39701715951532268261740949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26467810634354845507827299 39701715951532268261740949)
          ·
            refine ⟨1861017935228075074769107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39701715951532268261740949 1861017935228075074769107)
            ·
              refine ⟨2791526902842112612153661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861017935228075074769107 2791526902842112612153661)
              ·
                refine ⟨1046822588565792229557623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791526902842112612153661 1046822588565792229557623)
                ·
                  refine ⟨1570233882848688344336435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046822588565792229557623 1570233882848688344336435)
                  ·
                    refine ⟨2355350824273032516504653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570233882848688344336435 2355350824273032516504653)
                    ·
                      refine ⟨883256559102387193689245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2355350824273032516504653 883256559102387193689245)
                      ·
                        rfl

theorem cell23_1720136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_1720136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720136 prefixEnd_1720136 := by exact prefixLift 1720136
  have htrace : WordTrace (prefixWord ++ tailWord_1720136) baseStart_1720136 baseEnd_1720136 := by
    simpa [prefixWord, tailWord_1720136, baseEnd_1720136] using wordTrace_append hprefix tailTrace_1720136
  have hstable : (prefixWord ++ tailWord_1720136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720136).length < 2 ^ (prefixWord ++ tailWord_1720136).sum := by decide
  have hdescent : baseEnd_1720136 < baseStart_1720136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720145 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1720145 : Nat := 118140960795 + 1720145 * 2 ^ 59
def prefixEnd_1720145 : Nat := 4983230072969 + 3 ^ 40 * 1720145 * 2
def baseEnd_1720145 : Nat := 883261180428277658476703

theorem tailTrace_1720145 : CollatzResearch.WordTrace tailWord_1720145 prefixEnd_1720145 883261180428277658476703 := by
  unfold tailWord_1720145
  simp only [CollatzResearch.WordTrace]
  refine ⟨62738842353215917222297889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41825894902143944814865259 62738842353215917222297889)
  ·
    refine ⟨47054131764911937916723417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62738842353215917222297889 47054131764911937916723417)
    ·
      refine ⟨35290598823683953437542563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47054131764911937916723417 35290598823683953437542563)
      ·
        refine ⟨52935898235525930156313845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35290598823683953437542563 52935898235525930156313845)
        ·
          refine ⟨4962740459580555952154423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52935898235525930156313845 4962740459580555952154423)
          ·
            refine ⟨7444110689370833928231635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962740459580555952154423 7444110689370833928231635)
            ·
              refine ⟨11166166034056250892347453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444110689370833928231635 11166166034056250892347453)
              ·
                refine ⟨4187312262771094084630295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11166166034056250892347453 4187312262771094084630295)
                ·
                  refine ⟨6280968394156641126945443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187312262771094084630295 6280968394156641126945443)
                  ·
                    refine ⟨9421452591234961690418165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280968394156641126945443 9421452591234961690418165)
                    ·
                      refine ⟨883261180428277658476703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9421452591234961690418165 883261180428277658476703)
                      ·
                        rfl

theorem cell23_1720145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1720145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720145 prefixEnd_1720145 := by exact prefixLift 1720145
  have htrace : WordTrace (prefixWord ++ tailWord_1720145) baseStart_1720145 baseEnd_1720145 := by
    simpa [prefixWord, tailWord_1720145, baseEnd_1720145] using wordTrace_append hprefix tailTrace_1720145
  have hstable : (prefixWord ++ tailWord_1720145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720145).length < 2 ^ (prefixWord ++ tailWord_1720145).sum := by decide
  have hdescent : baseEnd_1720145 < baseStart_1720145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720159 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 3, 2, 2]
def baseStart_1720159 : Nat := 118140960795 + 1720159 * 2 ^ 59
def prefixEnd_1720159 : Nat := 4983230072969 + 3 ^ 40 * 1720159 * 2
def baseEnd_1720159 : Nat := 883268369157440603701639

theorem tailTrace_1720159 : CollatzResearch.WordTrace tailWord_1720159 prefixEnd_1720159 883268369157440603701639 := by
  unfold tailWord_1720159
  simp only [CollatzResearch.WordTrace]
  refine ⟨62739352975165197613307531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41826235316776798408871687 62739352975165197613307531)
  ·
    refine ⟨94109029462747796419961297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62739352975165197613307531 94109029462747796419961297)
    ·
      refine ⟨70581772097060847314970973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94109029462747796419961297 70581772097060847314970973)
      ·
        refine ⟨26468164536397817743114115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70581772097060847314970973 26468164536397817743114115)
        ·
          refine ⟨39702246804596726614671173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26468164536397817743114115 39702246804596726614671173)
          ·
            refine ⟨7444171275861886240250845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39702246804596726614671173 7444171275861886240250845)
            ·
              refine ⟨2791564228448207340094067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7444171275861886240250845 2791564228448207340094067)
              ·
                refine ⟨4187346342672311010141101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791564228448207340094067 4187346342672311010141101)
                ·
                  refine ⟨1570254878502116628802913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4187346342672311010141101 1570254878502116628802913)
                  ·
                    refine ⟨1177691158876587471602185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570254878502116628802913 1177691158876587471602185)
                    ·
                      refine ⟨883268369157440603701639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177691158876587471602185 883268369157440603701639)
                      ·
                        rfl

theorem cell23_1720159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_1720159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720159 prefixEnd_1720159 := by exact prefixLift 1720159
  have htrace : WordTrace (prefixWord ++ tailWord_1720159) baseStart_1720159 baseEnd_1720159 := by
    simpa [prefixWord, tailWord_1720159, baseEnd_1720159] using wordTrace_append hprefix tailTrace_1720159
  have hstable : (prefixWord ++ tailWord_1720159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720159).length < 2 ^ (prefixWord ++ tailWord_1720159).sum := by decide
  have hdescent : baseEnd_1720159 < baseStart_1720159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720162 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1720162 : Nat := 118140960795 + 1720162 * 2 ^ 59
def prefixEnd_1720162 : Nat := 4983230072969 + 3 ^ 40 * 1720162 * 2
def baseEnd_1720162 : Nat := 883269909599404091964125

theorem tailTrace_1720162 : CollatzResearch.WordTrace tailWord_1720162 prefixEnd_1720162 883269909599404091964125 := by
  unfold tailWord_1720162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15684865598538582281416685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41826308262769552750444493 15684865598538582281416685)
  ·
    refine ⟨5881824599451968355531257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15684865598538582281416685 5881824599451968355531257)
    ·
      refine ⟨4411368449588976266648443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5881824599451968355531257 4411368449588976266648443)
      ·
        refine ⟨6617052674383464399972665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411368449588976266648443 6617052674383464399972665)
        ·
          refine ⟨4962789505787598299979499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6617052674383464399972665 4962789505787598299979499)
          ·
            refine ⟨7444184258681397449969249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962789505787598299979499 7444184258681397449969249)
            ·
              refine ⟨5583138194011048087476937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444184258681397449969249 5583138194011048087476937)
              ·
                refine ⟨4187353645508286065607703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5583138194011048087476937 4187353645508286065607703)
                ·
                  refine ⟨6281030468262429098411555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187353645508286065607703 6281030468262429098411555)
                  ·
                    refine ⟨9421545702393643647617333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6281030468262429098411555 9421545702393643647617333)
                    ·
                      refine ⟨883269909599404091964125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9421545702393643647617333 883269909599404091964125)
                      ·
                        rfl

theorem cell23_1720162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1720162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720162 prefixEnd_1720162 := by exact prefixLift 1720162
  have htrace : WordTrace (prefixWord ++ tailWord_1720162) baseStart_1720162 baseEnd_1720162 := by
    simpa [prefixWord, tailWord_1720162, baseEnd_1720162] using wordTrace_append hprefix tailTrace_1720162
  have hstable : (prefixWord ++ tailWord_1720162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720162).length < 2 ^ (prefixWord ++ tailWord_1720162).sum := by decide
  have hdescent : baseEnd_1720162 < baseStart_1720162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720210 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1720210 : Nat := 118140960795 + 1720210 * 2 ^ 59
def prefixEnd_1720210 : Nat := 4983230072969 + 3 ^ 40 * 1720210 * 2
def baseEnd_1720210 : Nat := 883294556670819904163905

theorem tailTrace_1720210 : CollatzResearch.WordTrace tailWord_1720210 prefixEnd_1720210 883294556670819904163905 := by
  unfold tailWord_1720210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685303274495108330853521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41827475398653622215609389 15685303274495108330853521)
  ·
    refine ⟨11763977455871331248140141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15685303274495108330853521 11763977455871331248140141)
    ·
      refine ⟨4411491545951749218052553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11763977455871331248140141 4411491545951749218052553)
      ·
        refine ⟨3308618659463811913539415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411491545951749218052553 3308618659463811913539415)
        ·
          refine ⟨4962927989195717870309123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308618659463811913539415 4962927989195717870309123)
          ·
            refine ⟨7444391983793576805463685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962927989195717870309123 7444391983793576805463685)
            ·
              refine ⟨1395823496961295651024441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7444391983793576805463685 1395823496961295651024441)
              ·
                refine ⟨1046867622720971738268331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395823496961295651024441 1046867622720971738268331)
                ·
                  refine ⟨1570301434081457607402497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046867622720971738268331 1570301434081457607402497)
                  ·
                    refine ⟨1177726075561093205551873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570301434081457607402497 1177726075561093205551873)
                    ·
                      refine ⟨883294556670819904163905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177726075561093205551873 883294556670819904163905)
                      ·
                        rfl

theorem cell23_1720210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1720210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720210 prefixEnd_1720210 := by exact prefixLift 1720210
  have htrace : WordTrace (prefixWord ++ tailWord_1720210) baseStart_1720210 baseEnd_1720210 := by
    simpa [prefixWord, tailWord_1720210, baseEnd_1720210] using wordTrace_append hprefix tailTrace_1720210
  have hstable : (prefixWord ++ tailWord_1720210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720210).length < 2 ^ (prefixWord ++ tailWord_1720210).sum := by decide
  have hdescent : baseEnd_1720210 < baseStart_1720210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720215 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1720215 : Nat := 118140960795 + 1720215 * 2 ^ 59
def prefixEnd_1720215 : Nat := 4983230072969 + 3 ^ 40 * 1720215 * 2
def baseEnd_1720215 : Nat := 883297124074092384601381

theorem tailTrace_1720215 : CollatzResearch.WordTrace tailWord_1720215 prefixEnd_1720215 883297124074092384601381 := by
  unfold tailWord_1720215
  simp only [CollatzResearch.WordTrace]
  refine ⟨62741395462962319177346099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41827596975308212784897399 62741395462962319177346099)
  ·
    refine ⟨94112093194443478766019149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62741395462962319177346099 94112093194443478766019149)
    ·
      refine ⟨35292034947916304537257181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94112093194443478766019149 35292034947916304537257181)
      ·
        refine ⟨13234513105468614201471443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35292034947916304537257181 13234513105468614201471443)
        ·
          refine ⟨19851769658202921302207165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234513105468614201471443 19851769658202921302207165)
          ·
            refine ⟨7444413621826095488327687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19851769658202921302207165 7444413621826095488327687)
            ·
              refine ⟨11166620432739143232491531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444413621826095488327687 11166620432739143232491531)
              ·
                refine ⟨16749930649108714848737297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166620432739143232491531 16749930649108714848737297)
                ·
                  refine ⟨12562447986831536136552973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16749930649108714848737297 12562447986831536136552973)
                  ·
                    refine ⟨4710917995061826051207365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12562447986831536136552973 4710917995061826051207365)
                    ·
                      refine ⟨883297124074092384601381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4710917995061826051207365 883297124074092384601381)
                      ·
                        rfl

theorem cell23_1720215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1720215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720215 prefixEnd_1720215 := by exact prefixLift 1720215
  have htrace : WordTrace (prefixWord ++ tailWord_1720215) baseStart_1720215 baseEnd_1720215 := by
    simpa [prefixWord, tailWord_1720215, baseEnd_1720215] using wordTrace_append hprefix tailTrace_1720215
  have hstable : (prefixWord ++ tailWord_1720215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720215).length < 2 ^ (prefixWord ++ tailWord_1720215).sum := by decide
  have hdescent : baseEnd_1720215 < baseStart_1720215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720249 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1720249 : Nat := 118140960795 + 1720249 * 2 ^ 59
def prefixEnd_1720249 : Nat := 4983230072969 + 3 ^ 40 * 1720249 * 2
def baseEnd_1720249 : Nat := 883314582416345251576225

theorem tailTrace_1720249 : CollatzResearch.WordTrace tailWord_1720249 prefixEnd_1720249 883314582416345251576225 := by
  unfold tailWord_1720249
  simp only [CollatzResearch.WordTrace]
  refine ⟨62742635544839142984083801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41828423696559428656055867 62742635544839142984083801)
  ·
    refine ⟨47056976658629357238062851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62742635544839142984083801 47056976658629357238062851)
    ·
      refine ⟨70585464987944035857094277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47056976658629357238062851 70585464987944035857094277)
      ·
        refine ⟨13234774685239506723205177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70585464987944035857094277 13234774685239506723205177)
        ·
          refine ⟨9926081013929630042403883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13234774685239506723205177 9926081013929630042403883)
          ·
            refine ⟨14889121520894445063605825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926081013929630042403883 14889121520894445063605825)
            ·
              refine ⟨11166841140670833797704369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14889121520894445063605825 11166841140670833797704369)
              ·
                refine ⟨8375130855503125348278277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166841140670833797704369 8375130855503125348278277)
                ·
                  refine ⟨1570337035406836002802177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8375130855503125348278277 1570337035406836002802177)
                  ·
                    refine ⟨1177752776555127002101633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570337035406836002802177 1177752776555127002101633)
                    ·
                      refine ⟨883314582416345251576225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177752776555127002101633 883314582416345251576225)
                      ·
                        rfl

theorem cell23_1720249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1720249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720249 prefixEnd_1720249 := by exact prefixLift 1720249
  have htrace : WordTrace (prefixWord ++ tailWord_1720249) baseStart_1720249 baseEnd_1720249 := by
    simpa [prefixWord, tailWord_1720249, baseEnd_1720249] using wordTrace_append hprefix tailTrace_1720249
  have hstable : (prefixWord ++ tailWord_1720249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720249).length < 2 ^ (prefixWord ++ tailWord_1720249).sum := by decide
  have hdescent : baseEnd_1720249 < baseStart_1720249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720253 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1720253 : Nat := 118140960795 + 1720253 * 2 ^ 59
def prefixEnd_1720253 : Nat := 4983230072969 + 3 ^ 40 * 1720253 * 2
def baseEnd_1720253 : Nat := 883316636338963235926207

theorem tailTrace_1720253 : CollatzResearch.WordTrace tailWord_1720253 prefixEnd_1720253 883316636338963235926207 := by
  unfold tailWord_1720253
  simp only [CollatzResearch.WordTrace]
  refine ⟨62742781436824651667229413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41828520957883101111486275 62742781436824651667229413)
  ·
    refine ⟨11764271519404622187605515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62742781436824651667229413 11764271519404622187605515)
    ·
      refine ⟨17646407279106933281408273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11764271519404622187605515 17646407279106933281408273)
      ·
        refine ⟨13234805459330199961056205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17646407279106933281408273 13234805459330199961056205)
        ·
          refine ⟨4963052047248824985396077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13234805459330199961056205 4963052047248824985396077)
          ·
            refine ⟨1861144517718309369523529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4963052047248824985396077 1861144517718309369523529)
            ·
              refine ⟨1395858388288732027142647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861144517718309369523529 1395858388288732027142647)
              ·
                refine ⟨2093787582433098040713971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395858388288732027142647 2093787582433098040713971)
                ·
                  refine ⟨3140681373649647061070957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093787582433098040713971 3140681373649647061070957)
                  ·
                    refine ⟨1177755515118617647901609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140681373649647061070957 1177755515118617647901609)
                    ·
                      refine ⟨883316636338963235926207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177755515118617647901609 883316636338963235926207)
                      ·
                        rfl

theorem cell23_1720253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1720253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720253 prefixEnd_1720253 := by exact prefixLift 1720253
  have htrace : WordTrace (prefixWord ++ tailWord_1720253) baseStart_1720253 baseEnd_1720253 := by
    simpa [prefixWord, tailWord_1720253, baseEnd_1720253] using wordTrace_append hprefix tailTrace_1720253
  have hstable : (prefixWord ++ tailWord_1720253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720253).length < 2 ^ (prefixWord ++ tailWord_1720253).sum := by decide
  have hdescent : baseEnd_1720253 < baseStart_1720253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720265 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_1720265 : Nat := 118140960795 + 1720265 * 2 ^ 59
def prefixEnd_1720265 : Nat := 4983230072969 + 3 ^ 40 * 1720265 * 2
def baseEnd_1720265 : Nat := 883322798106817188976151

theorem tailTrace_1720265 : CollatzResearch.WordTrace tailWord_1720265 prefixEnd_1720265 883322798106817188976151 := by
  unfold tailWord_1720265
  simp only [CollatzResearch.WordTrace]
  refine ⟨62743219112781177716666249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41828812741854118477777499 62743219112781177716666249)
  ·
    refine ⟨47057414334585883287499687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62743219112781177716666249 47057414334585883287499687)
    ·
      refine ⟨70586121501878824931249531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47057414334585883287499687 70586121501878824931249531)
      ·
        refine ⟨105879182252818237396874297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70586121501878824931249531 105879182252818237396874297)
        ·
          refine ⟨79409386689613678047655723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105879182252818237396874297 79409386689613678047655723)
          ·
            refine ⟨119114080034420517071483585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79409386689613678047655723 119114080034420517071483585)
            ·
              refine ⟨89335560025815387803612689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119114080034420517071483585 89335560025815387803612689)
              ·
                refine ⟨67001670019361540852709517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89335560025815387803612689 67001670019361540852709517)
                ·
                  refine ⟨25125626257260577819766069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67001670019361540852709517 25125626257260577819766069)
                  ·
                    refine ⟨2355527461618179170603069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25125626257260577819766069 2355527461618179170603069)
                    ·
                      refine ⟨883322798106817188976151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2355527461618179170603069 883322798106817188976151)
                      ·
                        rfl

theorem cell23_1720265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_1720265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720265 prefixEnd_1720265 := by exact prefixLift 1720265
  have htrace : WordTrace (prefixWord ++ tailWord_1720265) baseStart_1720265 baseEnd_1720265 := by
    simpa [prefixWord, tailWord_1720265, baseEnd_1720265] using wordTrace_append hprefix tailTrace_1720265
  have hstable : (prefixWord ++ tailWord_1720265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720265).length < 2 ^ (prefixWord ++ tailWord_1720265).sum := by decide
  have hdescent : baseEnd_1720265 < baseStart_1720265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720266 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_1720266 : Nat := 118140960795 + 1720266 * 2 ^ 59
def prefixEnd_1720266 : Nat := 4983230072969 + 3 ^ 40 * 1720266 * 2
def baseEnd_1720266 : Nat := 883323311587471685063647

theorem tailTrace_1720266 : CollatzResearch.WordTrace tailWord_1720266 prefixEnd_1720266 883323311587471685063647 := by
  unfold tailWord_1720266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685813896444388721863163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41828837057185036591635101 15685813896444388721863163)
  ·
    refine ⟨23528720844666583082794745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15685813896444388721863163 23528720844666583082794745)
    ·
      refine ⟨17646540633499937312096059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23528720844666583082794745 17646540633499937312096059)
      ·
        refine ⟨26469810950249905968144089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17646540633499937312096059 26469810950249905968144089)
        ·
          refine ⟨19852358212687429476108067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26469810950249905968144089 19852358212687429476108067)
          ·
            refine ⟨29778537319031144214162101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19852358212687429476108067 29778537319031144214162101)
            ·
              refine ⟨2791737873659169770077697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29778537319031144214162101 2791737873659169770077697)
              ·
                refine ⟨2093803405244377327558273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791737873659169770077697 2093803405244377327558273)
                ·
                  refine ⟨1570352553933282995668705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093803405244377327558273 1570352553933282995668705)
                  ·
                    refine ⟨1177764415449962246751529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570352553933282995668705 1177764415449962246751529)
                    ·
                      refine ⟨883323311587471685063647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177764415449962246751529 883323311587471685063647)
                      ·
                        rfl

theorem cell23_1720266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_1720266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720266 prefixEnd_1720266 := by exact prefixLift 1720266
  have htrace : WordTrace (prefixWord ++ tailWord_1720266) baseStart_1720266 baseEnd_1720266 := by
    simpa [prefixWord, tailWord_1720266, baseEnd_1720266] using wordTrace_append hprefix tailTrace_1720266
  have hstable : (prefixWord ++ tailWord_1720266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720266).length < 2 ^ (prefixWord ++ tailWord_1720266).sum := by decide
  have hdescent : baseEnd_1720266 < baseStart_1720266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720272 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 5]
def baseStart_1720272 : Nat := 118140960795 + 1720272 * 2 ^ 59
def prefixEnd_1720272 : Nat := 4983230072969 + 3 ^ 40 * 1720272 * 2
def baseEnd_1720272 : Nat := 98147376941266517954291

theorem tailTrace_1720272 : CollatzResearch.WordTrace tailWord_1720272 prefixEnd_1720272 98147376941266517954291 := by
  unfold tailWord_1720272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31371737211877908956085535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41828982949170545274780713 31371737211877908956085535)
  ·
    refine ⟨47057605817816863434128303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31371737211877908956085535 47057605817816863434128303)
    ·
      refine ⟨70586408726725295151192455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47057605817816863434128303 70586408726725295151192455)
      ·
        refine ⟨105879613090087942726788683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70586408726725295151192455 105879613090087942726788683)
        ·
          refine ⟨158819419635131914090183025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105879613090087942726788683 158819419635131914090183025)
          ·
            refine ⟨119114564726348935567637269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158819419635131914090183025 119114564726348935567637269)
            ·
              refine ⟨5583495221547606354732997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119114564726348935567637269 5583495221547606354732997)
              ·
                refine ⟨1046905354040176191512437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5583495221547606354732997 1046905354040176191512437)
                ·
                  refine ⟨98147376941266517954291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046905354040176191512437 98147376941266517954291)
                  ·
                    rfl

theorem cell23_1720272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 5].length) (baseStart_1720272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720272 prefixEnd_1720272 := by exact prefixLift 1720272
  have htrace : WordTrace (prefixWord ++ tailWord_1720272) baseStart_1720272 baseEnd_1720272 := by
    simpa [prefixWord, tailWord_1720272, baseEnd_1720272] using wordTrace_append hprefix tailTrace_1720272
  have hstable : (prefixWord ++ tailWord_1720272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720272).length < 2 ^ (prefixWord ++ tailWord_1720272).sum := by decide
  have hdescent : baseEnd_1720272 < baseStart_1720272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720302 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1720302 : Nat := 118140960795 + 1720302 * 2 ^ 59
def prefixEnd_1720302 : Nat := 4983230072969 + 3 ^ 40 * 1720302 * 2
def baseEnd_1720302 : Nat := 294447265630344514737827

theorem tailTrace_1720302 : CollatzResearch.WordTrace tailWord_1720302 prefixEnd_1720302 294447265630344514737827 := by
  unfold tailWord_1720302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843071076705891629470395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41829712409098088690508773 7843071076705891629470395)
  ·
    refine ⟨11764606615058837444205593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843071076705891629470395 11764606615058837444205593)
    ·
      refine ⟨8823454961294128083154195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11764606615058837444205593 8823454961294128083154195)
      ·
        refine ⟨13235182441941192124731293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8823454961294128083154195 13235182441941192124731293)
        ·
          refine ⟨4963193415727947046774235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13235182441941192124731293 4963193415727947046774235)
          ·
            refine ⟨7444790123591920570161353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963193415727947046774235 7444790123591920570161353)
            ·
              refine ⟨5583592592693940427621015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444790123591920570161353 5583592592693940427621015)
              ·
                refine ⟨8375388889040910641431523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583592592693940427621015 8375388889040910641431523)
                ·
                  refine ⟨12563083333561365962147285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8375388889040910641431523 12563083333561365962147285)
                  ·
                    refine ⟨294447265630344514737827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12563083333561365962147285 294447265630344514737827)
                    ·
                      rfl

theorem cell23_1720302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1720302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720302 prefixEnd_1720302 := by exact prefixLift 1720302
  have htrace : WordTrace (prefixWord ++ tailWord_1720302) baseStart_1720302 baseEnd_1720302 := by
    simpa [prefixWord, tailWord_1720302, baseEnd_1720302] using wordTrace_append hprefix tailTrace_1720302
  have hstable : (prefixWord ++ tailWord_1720302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720302).length < 2 ^ (prefixWord ++ tailWord_1720302).sum := by decide
  have hdescent : baseEnd_1720302 < baseStart_1720302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720356 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1720356 : Nat := 118140960795 + 1720356 * 2 ^ 59
def prefixEnd_1720356 : Nat := 4983230072969 + 3 ^ 40 * 1720356 * 2
def baseEnd_1720356 : Nat := 883369524846376332938233

theorem tailTrace_1720356 : CollatzResearch.WordTrace tailWord_1720356 prefixEnd_1720356 883369524846376332938233 := by
  unfold tailWord_1720356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373269077725750129114461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41831025436967666838819281 31373269077725750129114461)
  ·
    refine ⟨11764975904147156298417923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31373269077725750129114461 11764975904147156298417923)
    ·
      refine ⟨17647463856220734447626885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11764975904147156298417923 17647463856220734447626885)
      ·
        refine ⟨3308899473041387708930041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17647463856220734447626885 3308899473041387708930041)
        ·
          refine ⟨2481674604781040781697531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308899473041387708930041 2481674604781040781697531)
          ·
            refine ⟨3722511907171561172546297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481674604781040781697531 3722511907171561172546297)
            ·
              refine ⟨2791883930378670879409723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722511907171561172546297 2791883930378670879409723)
              ·
                refine ⟨4187825895568006319114585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791883930378670879409723 4187825895568006319114585)
                ·
                  refine ⟨3140869421676004739335939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187825895568006319114585 3140869421676004739335939)
                  ·
                    refine ⟨4711304132514007109003909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3140869421676004739335939 4711304132514007109003909)
                    ·
                      refine ⟨883369524846376332938233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4711304132514007109003909 883369524846376332938233)
                      ·
                        rfl

theorem cell23_1720356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1720356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720356 prefixEnd_1720356 := by exact prefixLift 1720356
  have htrace : WordTrace (prefixWord ++ tailWord_1720356) baseStart_1720356 baseEnd_1720356 := by
    simpa [prefixWord, tailWord_1720356, baseEnd_1720356] using wordTrace_append hprefix tailTrace_1720356
  have hstable : (prefixWord ++ tailWord_1720356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720356).length < 2 ^ (prefixWord ++ tailWord_1720356).sum := by decide
  have hdescent : baseEnd_1720356 < baseStart_1720356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720389 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_1720389 : Nat := 118140960795 + 1720389 * 2 ^ 59
def prefixEnd_1720389 : Nat := 4983230072969 + 3 ^ 40 * 1720389 * 2
def baseEnd_1720389 : Nat := 883386469707974703825581

theorem tailTrace_1720389 : CollatzResearch.WordTrace tailWord_1720389 prefixEnd_1720389 883386469707974703825581 := by
  unfold tailWord_1720389
  simp only [CollatzResearch.WordTrace]
  refine ⟨62747741764331946894180221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41831827842887964596120147 62747741764331946894180221)
  ·
    refine ⟨23530403161624480085317583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62747741764331946894180221 23530403161624480085317583)
    ·
      refine ⟨35295604742436720127976375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23530403161624480085317583 35295604742436720127976375)
      ·
        refine ⟨52943407113655080191964563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35295604742436720127976375 52943407113655080191964563)
        ·
          refine ⟨79415110670482620287946845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52943407113655080191964563 79415110670482620287946845)
          ·
            refine ⟨29780666501430982607980067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79415110670482620287946845 29780666501430982607980067)
            ·
              refine ⟨44670999752146473911970101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29780666501430982607980067 44670999752146473911970101)
              ·
                refine ⟨4187906226763731929247197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44670999752146473911970101 4187906226763731929247197)
                ·
                  refine ⟨1570464835036399473467699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4187906226763731929247197 1570464835036399473467699)
                  ·
                    refine ⟨2355697252554599210201549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570464835036399473467699 2355697252554599210201549)
                    ·
                      refine ⟨883386469707974703825581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2355697252554599210201549 883386469707974703825581)
                      ·
                        rfl

theorem cell23_1720389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_1720389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720389 prefixEnd_1720389 := by exact prefixLift 1720389
  have htrace : WordTrace (prefixWord ++ tailWord_1720389) baseStart_1720389 baseEnd_1720389 := by
    simpa [prefixWord, tailWord_1720389, baseEnd_1720389] using wordTrace_append hprefix tailTrace_1720389
  have hstable : (prefixWord ++ tailWord_1720389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720389).length < 2 ^ (prefixWord ++ tailWord_1720389).sum := by decide
  have hdescent : baseEnd_1720389 < baseStart_1720389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720416 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2]
def baseStart_1720416 : Nat := 118140960795 + 1720416 * 2 ^ 59
def prefixEnd_1720416 : Nat := 4983230072969 + 3 ^ 40 * 1720416 * 2
def baseEnd_1720416 : Nat := 883400333685646098187957

theorem tailTrace_1720416 : CollatzResearch.WordTrace tailWord_1720416 prefixEnd_1720416 883400333685646098187957 := by
  unfold tailWord_1720416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31374363267617065252706551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41832484356822753670275401 31374363267617065252706551)
  ·
    refine ⟨47061544901425597879059827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31374363267617065252706551 47061544901425597879059827)
    ·
      refine ⟨70592317352138396818589741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47061544901425597879059827 70592317352138396818589741)
      ·
        refine ⟨26472119007051898806971153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70592317352138396818589741 26472119007051898806971153)
        ·
          refine ⟨19854089255288924105228365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26472119007051898806971153 19854089255288924105228365)
          ·
            refine ⟨7445283470733346539460637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19854089255288924105228365 7445283470733346539460637)
            ·
              refine ⟨2791981301525004952297739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7445283470733346539460637 2791981301525004952297739)
              ·
                refine ⟨4187971952287507428446609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791981301525004952297739 4187971952287507428446609)
                ·
                  refine ⟨3140978964215630571334957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187971952287507428446609 3140978964215630571334957)
                  ·
                    refine ⟨1177867111580861464250609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140978964215630571334957 1177867111580861464250609)
                    ·
                      refine ⟨883400333685646098187957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177867111580861464250609 883400333685646098187957)
                      ·
                        rfl

theorem cell23_1720416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_1720416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720416 prefixEnd_1720416 := by exact prefixLift 1720416
  have htrace : WordTrace (prefixWord ++ tailWord_1720416) baseStart_1720416 baseEnd_1720416 := by
    simpa [prefixWord, tailWord_1720416, baseEnd_1720416] using wordTrace_append hprefix tailTrace_1720416
  have hstable : (prefixWord ++ tailWord_1720416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720416).length < 2 ^ (prefixWord ++ tailWord_1720416).sum := by decide
  have hdescent : baseEnd_1720416 < baseStart_1720416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720423 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_1720423 : Nat := 118140960795 + 1720423 * 2 ^ 59
def prefixEnd_1720423 : Nat := 4983230072969 + 3 ^ 40 * 1720423 * 2
def baseEnd_1720423 : Nat := 883403928050227570800425

theorem tailTrace_1720423 : CollatzResearch.WordTrace tailWord_1720423 prefixEnd_1720423 883403928050227570800425 := by
  unfold tailWord_1720423
  simp only [CollatzResearch.WordTrace]
  refine ⟨62748981846208770700917923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41832654564139180467278615 62748981846208770700917923)
  ·
    refine ⟨94123472769313156051376885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62748981846208770700917923 94123472769313156051376885)
    ·
      refine ⟨8824075572123108379816583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94123472769313156051376885 8824075572123108379816583)
      ·
        refine ⟨13236113358184662569724875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824075572123108379816583 13236113358184662569724875)
        ·
          refine ⟨19854170037276993854587313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13236113358184662569724875 19854170037276993854587313)
          ·
            refine ⟨14890627527957745390940485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19854170037276993854587313 14890627527957745390940485)
            ·
              refine ⟨2791992661492077260801341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14890627527957745390940485 2791992661492077260801341)
              ·
                refine ⟨1046997248059528972800503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791992661492077260801341 1046997248059528972800503)
                ·
                  refine ⟨1570495872089293459200755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046997248059528972800503 1570495872089293459200755)
                  ·
                    refine ⟨2355743808133940188801133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570495872089293459200755 2355743808133940188801133)
                    ·
                      refine ⟨883403928050227570800425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2355743808133940188801133 883403928050227570800425)
                      ·
                        rfl

theorem cell23_1720423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_1720423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720423 prefixEnd_1720423 := by exact prefixLift 1720423
  have htrace : WordTrace (prefixWord ++ tailWord_1720423) baseStart_1720423 baseEnd_1720423 := by
    simpa [prefixWord, tailWord_1720423, baseEnd_1720423] using wordTrace_append hprefix tailTrace_1720423
  have hstable : (prefixWord ++ tailWord_1720423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720423).length < 2 ^ (prefixWord ++ tailWord_1720423).sum := by decide
  have hdescent : baseEnd_1720423 < baseStart_1720423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720426 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1720426 : Nat := 118140960795 + 1720426 * 2 ^ 59
def prefixEnd_1720426 : Nat := 4983230072969 + 3 ^ 40 * 1720426 * 2
def baseEnd_1720426 : Nat := 294468489497397019687637

theorem tailTrace_1720426 : CollatzResearch.WordTrace tailWord_1720426 prefixEnd_1720426 294468489497397019687637 := by
  unfold tailWord_1720426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15687272816299475553319283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41832727510131934808851421 15687272816299475553319283)
  ·
    refine ⟨23530909224449213329978925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15687272816299475553319283 23530909224449213329978925)
    ·
      refine ⟨8824090959168454998742097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23530909224449213329978925 8824090959168454998742097)
      ·
        refine ⟨6618068219376341249056573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8824090959168454998742097 6618068219376341249056573)
        ·
          refine ⟨2481775582266127968396215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6618068219376341249056573 2481775582266127968396215)
          ·
            refine ⟨3722663373399191952594323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481775582266127968396215 3722663373399191952594323)
            ·
              refine ⟨5583995060098787928891485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722663373399191952594323 5583995060098787928891485)
              ·
                refine ⟨2093998147537045473334307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5583995060098787928891485 2093998147537045473334307)
                ·
                  refine ⟨3140997221305568210001461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093998147537045473334307 3140997221305568210001461)
                  ·
                    refine ⟨294468489497397019687637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3140997221305568210001461 294468489497397019687637)
                    ·
                      rfl

theorem cell23_1720426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1720426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720426 prefixEnd_1720426 := by exact prefixLift 1720426
  have htrace : WordTrace (prefixWord ++ tailWord_1720426) baseStart_1720426 baseEnd_1720426 := by
    simpa [prefixWord, tailWord_1720426, baseEnd_1720426] using wordTrace_append hprefix tailTrace_1720426
  have hstable : (prefixWord ++ tailWord_1720426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720426).length < 2 ^ (prefixWord ++ tailWord_1720426).sum := by decide
  have hdescent : baseEnd_1720426 < baseStart_1720426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720439 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 4, 4]
def baseStart_1720439 : Nat := 118140960795 + 1720439 * 2 ^ 59
def prefixEnd_1720439 : Nat := 4983230072969 + 3 ^ 40 * 1720439 * 2
def baseEnd_1720439 : Nat := 294470714580233169400117

theorem tailTrace_1720439 : CollatzResearch.WordTrace tailWord_1720439 prefixEnd_1720439 294470714580233169400117 := by
  unfold tailWord_1720439
  simp only [CollatzResearch.WordTrace]
  refine ⟨62749565414150805433500371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41833043609433870289000247 62749565414150805433500371)
  ·
    refine ⟨94124348121226208150250557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62749565414150805433500371 94124348121226208150250557)
    ·
      refine ⟨35296630545459828056343959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94124348121226208150250557 35296630545459828056343959)
      ·
        refine ⟨52944945818189742084515939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35296630545459828056343959 52944945818189742084515939)
        ·
          refine ⟨79417418727284613126773909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52944945818189742084515939 79417418727284613126773909)
          ·
            refine ⟨3722691502841466240317527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79417418727284613126773909 3722691502841466240317527)
            ·
              refine ⟨5584037254262199360476291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722691502841466240317527 5584037254262199360476291)
              ·
                refine ⟨8376055881393299040714437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584037254262199360476291 8376055881393299040714437)
                ·
                  refine ⟨1570510477761243570133957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8376055881393299040714437 1570510477761243570133957)
                  ·
                    refine ⟨294470714580233169400117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1570510477761243570133957 294470714580233169400117)
                    ·
                      rfl

theorem cell23_1720439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_1720439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720439 prefixEnd_1720439 := by exact prefixLift 1720439
  have htrace : WordTrace (prefixWord ++ tailWord_1720439) baseStart_1720439 baseEnd_1720439 := by
    simpa [prefixWord, tailWord_1720439, baseEnd_1720439] using wordTrace_append hprefix tailTrace_1720439
  have hstable : (prefixWord ++ tailWord_1720439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720439).length < 2 ^ (prefixWord ++ tailWord_1720439).sum := by decide
  have hdescent : baseEnd_1720439 < baseStart_1720439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720452 : List Nat := [2, 3, 2, 1, 2, 1, 2, 10]
def baseStart_1720452 : Nat := 118140960795 + 1720452 * 2 ^ 59
def prefixEnd_1720452 : Nat := 4983230072969 + 3 ^ 40 * 1720452 * 2
def baseEnd_1720452 : Nat := 32719215518118813234733

theorem tailTrace_1720452 : CollatzResearch.WordTrace tailWord_1720452 prefixEnd_1720452 32719215518118813234733 := by
  unfold tailWord_1720452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31375019781551854326861805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41833359708735805769149073 31375019781551854326861805)
  ·
    refine ⟨11765632418081945372573177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31375019781551854326861805 11765632418081945372573177)
    ·
      refine ⟨8824224313561459029429883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11765632418081945372573177 8824224313561459029429883)
      ·
        refine ⟨13236336470342188544144825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824224313561459029429883 13236336470342188544144825)
        ·
          refine ⟨9927252352756641408108619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13236336470342188544144825 9927252352756641408108619)
          ·
            refine ⟨14890878529134962112162929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927252352756641408108619 14890878529134962112162929)
            ·
              refine ⟨11168158896851221584122197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14890878529134962112162929 11168158896851221584122197)
              ·
                refine ⟨32719215518118813234733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11168158896851221584122197 32719215518118813234733)
                ·
                  rfl

theorem cell23_1720452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 10].length) (baseStart_1720452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720452 prefixEnd_1720452 := by exact prefixLift 1720452
  have htrace : WordTrace (prefixWord ++ tailWord_1720452) baseStart_1720452 baseEnd_1720452 := by
    simpa [prefixWord, tailWord_1720452, baseEnd_1720452] using wordTrace_append hprefix tailTrace_1720452
  have hstable : (prefixWord ++ tailWord_1720452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720452).length < 2 ^ (prefixWord ++ tailWord_1720452).sum := by decide
  have hdescent : baseEnd_1720452 < baseStart_1720452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720456 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1720456 : Nat := 118140960795 + 1720456 * 2 ^ 59
def prefixEnd_1720456 : Nat := 4983230072969 + 3 ^ 40 * 1720456 * 2
def baseEnd_1720456 : Nat := 294473624303941980562591

theorem tailTrace_1720456 : CollatzResearch.WordTrace tailWord_1720456 prefixEnd_1720456 294473624303941980562591 := by
  unfold tailWord_1720456
  simp only [CollatzResearch.WordTrace]
  refine ⟨31375092727544608668434611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41833456970059478224579481 31375092727544608668434611)
  ·
    refine ⟨47062639091316913002651917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31375092727544608668434611 47062639091316913002651917)
    ·
      refine ⟨17648489659243842375994469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47062639091316913002651917 17648489659243842375994469)
      ·
        refine ⟨3309091811108220445498963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17648489659243842375994469 3309091811108220445498963)
        ·
          refine ⟨4963637716662330668248445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309091811108220445498963 4963637716662330668248445)
          ·
            refine ⟨1861364143748374000593167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4963637716662330668248445 1861364143748374000593167)
            ·
              refine ⟨2792046215622561000889751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861364143748374000593167 2792046215622561000889751)
              ·
                refine ⟨4188069323433841501334627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792046215622561000889751 4188069323433841501334627)
                ·
                  refine ⟨6282103985150762252001941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188069323433841501334627 6282103985150762252001941)
                  ·
                    refine ⟨294473624303941980562591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6282103985150762252001941 294473624303941980562591)
                    ·
                      rfl

theorem cell23_1720456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1720456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720456 prefixEnd_1720456 := by exact prefixLift 1720456
  have htrace : WordTrace (prefixWord ++ tailWord_1720456) baseStart_1720456 baseEnd_1720456 := by
    simpa [prefixWord, tailWord_1720456, baseEnd_1720456] using wordTrace_append hprefix tailTrace_1720456
  have hstable : (prefixWord ++ tailWord_1720456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720456).length < 2 ^ (prefixWord ++ tailWord_1720456).sum := by decide
  have hdescent : baseEnd_1720456 < baseStart_1720456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720480 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 1, 2, 2]
def baseStart_1720480 : Nat := 118140960795 + 1720480 * 2 ^ 59
def prefixEnd_1720480 : Nat := 4983230072969 + 3 ^ 40 * 1720480 * 2
def baseEnd_1720480 : Nat := 883433196447533847787663

theorem tailTrace_1720480 : CollatzResearch.WordTrace tailWord_1720480 prefixEnd_1720480 883433196447533847787663 := by
  unfold tailWord_1720480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31375530403501134717871447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41834040538001512957161929 31375530403501134717871447)
  ·
    refine ⟨47063295605251702076807171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31375530403501134717871447 47063295605251702076807171)
    ·
      refine ⟨70594943407877553115210757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47063295605251702076807171 70594943407877553115210757)
      ·
        refine ⟨13236551888977041209102017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70594943407877553115210757 13236551888977041209102017)
        ·
          refine ⟨9927413916732780906826513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13236551888977041209102017 9927413916732780906826513)
          ·
            refine ⟨7445560437549585680119885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9927413916732780906826513 7445560437549585680119885)
            ·
              refine ⟨2792085164081094630044957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7445560437549585680119885 2792085164081094630044957)
              ·
                refine ⟨1047031936530410486266859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2792085164081094630044957 1047031936530410486266859)
                ·
                  refine ⟨1570547904795615729400289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047031936530410486266859 1570547904795615729400289)
                  ·
                    refine ⟨1177910928596711797050217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570547904795615729400289 1177910928596711797050217)
                    ·
                      refine ⟨883433196447533847787663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177910928596711797050217 883433196447533847787663)
                      ·
                        rfl

theorem cell23_1720480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_1720480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720480 prefixEnd_1720480 := by exact prefixLift 1720480
  have htrace : WordTrace (prefixWord ++ tailWord_1720480) baseStart_1720480 baseEnd_1720480 := by
    simpa [prefixWord, tailWord_1720480, baseEnd_1720480] using wordTrace_append hprefix tailTrace_1720480
  have hstable : (prefixWord ++ tailWord_1720480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720480).length < 2 ^ (prefixWord ++ tailWord_1720480).sum := by decide
  have hdescent : baseEnd_1720480 < baseStart_1720480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720497 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1720497 : Nat := 118140960795 + 1720497 * 2 ^ 59
def prefixEnd_1720497 : Nat := 4983230072969 + 3 ^ 40 * 1720497 * 2
def baseEnd_1720497 : Nat := 883441925618660281275085

theorem tailTrace_1720497 : CollatzResearch.WordTrace tailWord_1720497 prefixEnd_1720497 883441925618660281275085 := by
  unfold tailWord_1720497
  simp only [CollatzResearch.WordTrace]
  refine ⟨62751680847940681339111745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41834453898627120892741163 62751680847940681339111745)
  ·
    refine ⟨47063760635955511004333809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62751680847940681339111745 47063760635955511004333809)
    ·
      refine ⟨35297820476966633253250357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47063760635955511004333809 35297820476966633253250357)
      ·
        refine ⟨3309170669715621867492221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35297820476966633253250357 3309170669715621867492221)
        ·
          refine ⟨1240939001143358200309583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3309170669715621867492221 1240939001143358200309583)
          ·
            refine ⟨1861408501715037300464375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240939001143358200309583 1861408501715037300464375)
            ·
              refine ⟨2792112752572555950696563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861408501715037300464375 2792112752572555950696563)
              ·
                refine ⟨4188169128858833926044845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792112752572555950696563 4188169128858833926044845)
                ·
                  refine ⟨1570563423322062722266817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4188169128858833926044845 1570563423322062722266817)
                  ·
                    refine ⟨1177922567491547041700113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570563423322062722266817 1177922567491547041700113)
                    ·
                      refine ⟨883441925618660281275085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177922567491547041700113 883441925618660281275085)
                      ·
                        rfl

theorem cell23_1720497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1720497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720497 prefixEnd_1720497 := by exact prefixLift 1720497
  have htrace : WordTrace (prefixWord ++ tailWord_1720497) baseStart_1720497 baseEnd_1720497 := by
    simpa [prefixWord, tailWord_1720497, baseEnd_1720497] using wordTrace_append hprefix tailTrace_1720497
  have hstable : (prefixWord ++ tailWord_1720497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720497).length < 2 ^ (prefixWord ++ tailWord_1720497).sum := by decide
  have hdescent : baseEnd_1720497 < baseStart_1720497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720536 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_1720536 : Nat := 118140960795 + 1720536 * 2 ^ 59
def prefixEnd_1720536 : Nat := 4983230072969 + 3 ^ 40 * 1720536 * 2
def baseEnd_1720536 : Nat := 883461951364185628687405

theorem tailTrace_1720536 : CollatzResearch.WordTrace tailWord_1720536 prefixEnd_1720536 883461951364185628687405 := by
  unfold tailWord_1720536
  simp only [CollatzResearch.WordTrace]
  refine ⟨31376551647399695499890731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41835402196532927333187641 31376551647399695499890731)
  ·
    refine ⟨47064827471099543249836097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31376551647399695499890731 47064827471099543249836097)
    ·
      refine ⟨35298620603324657437377073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47064827471099543249836097 35298620603324657437377073)
      ·
        refine ⟨26473965452493493078032805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35298620603324657437377073 26473965452493493078032805)
        ·
          refine ⟨4963868522342529952131151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26473965452493493078032805 4963868522342529952131151)
          ·
            refine ⟨7445802783513794928196727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963868522342529952131151 7445802783513794928196727)
            ·
              refine ⟨11168704175270692392295091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445802783513794928196727 11168704175270692392295091)
              ·
                refine ⟨16753056262906038588442637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168704175270692392295091 16753056262906038588442637)
                ·
                  refine ⟨6282396098589764470665989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16753056262906038588442637 6282396098589764470665989)
                  ·
                    refine ⟨1177949268485580838249873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282396098589764470665989 1177949268485580838249873)
                    ·
                      refine ⟨883461951364185628687405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1177949268485580838249873 883461951364185628687405)
                      ·
                        rfl

theorem cell23_1720536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_1720536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720536 prefixEnd_1720536 := by exact prefixLift 1720536
  have htrace : WordTrace (prefixWord ++ tailWord_1720536) baseStart_1720536 baseEnd_1720536 := by
    simpa [prefixWord, tailWord_1720536, baseEnd_1720536] using wordTrace_append hprefix tailTrace_1720536
  have hstable : (prefixWord ++ tailWord_1720536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720536).length < 2 ^ (prefixWord ++ tailWord_1720536).sum := by decide
  have hdescent : baseEnd_1720536 < baseStart_1720536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720636 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_1720636 : Nat := 118140960795 + 1720636 * 2 ^ 59
def prefixEnd_1720636 : Nat := 4983230072969 + 3 ^ 40 * 1720636 * 2
def baseEnd_1720636 : Nat := 294504433143211745812315

theorem tailTrace_1720636 : CollatzResearch.WordTrace tailWord_1720636 prefixEnd_1720636 294504433143211745812315 := by
  unfold tailWord_1720636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31378375297218554039210881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41837833729624738718947841 31378375297218554039210881)
  ·
    refine ⟨23533781472913915529408161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31378375297218554039210881 23533781472913915529408161)
    ·
      refine ⟨17650336104685436647056121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23533781472913915529408161 17650336104685436647056121)
      ·
        refine ⟨13237752078514077485292091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17650336104685436647056121 13237752078514077485292091)
        ·
          refine ⟨19856628117771116227938137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13237752078514077485292091 19856628117771116227938137)
          ·
            refine ⟨14892471088328337170953603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19856628117771116227938137 14892471088328337170953603)
            ·
              refine ⟨22338706632492505756430405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892471088328337170953603 22338706632492505756430405)
              ·
                refine ⟨4188507493592344829330701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22338706632492505756430405 4188507493592344829330701)
                ·
                  refine ⟨1570690310097129310999013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4188507493592344829330701 1570690310097129310999013)
                  ·
                    refine ⟨294504433143211745812315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1570690310097129310999013 294504433143211745812315)
                    ·
                      rfl

theorem cell23_1720636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_1720636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720636 prefixEnd_1720636 := by exact prefixLift 1720636
  have htrace : WordTrace (prefixWord ++ tailWord_1720636) baseStart_1720636 baseEnd_1720636 := by
    simpa [prefixWord, tailWord_1720636, baseEnd_1720636] using wordTrace_append hprefix tailTrace_1720636
  have hstable : (prefixWord ++ tailWord_1720636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720636).length < 2 ^ (prefixWord ++ tailWord_1720636).sum := by decide
  have hdescent : baseEnd_1720636 < baseStart_1720636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720639 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1720639 : Nat := 118140960795 + 1720639 * 2 ^ 59
def prefixEnd_1720639 : Nat := 4983230072969 + 3 ^ 40 * 1720639 * 2
def baseEnd_1720639 : Nat := 883514839871598725699431

theorem tailTrace_1720639 : CollatzResearch.WordTrace tailWord_1720639 prefixEnd_1720639 883514839871598725699431 := by
  unfold tailWord_1720639
  simp only [CollatzResearch.WordTrace]
  refine ⟨62756860013426239590780971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41837906675617493060520647 62756860013426239590780971)
  ·
    refine ⟨94135290020139359386171457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62756860013426239590780971 94135290020139359386171457)
    ·
      refine ⟨70601467515104519539628593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94135290020139359386171457 70601467515104519539628593)
      ·
        refine ⟨52951100636328389654721445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70601467515104519539628593 52951100636328389654721445)
        ·
          refine ⟨9928331369311573060260271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52951100636328389654721445 9928331369311573060260271)
          ·
            refine ⟨14892497053967359590390407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9928331369311573060260271 14892497053967359590390407)
            ·
              refine ⟨22338745580951039385585611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892497053967359590390407 22338745580951039385585611)
              ·
                refine ⟨33508118371426559078378417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22338745580951039385585611 33508118371426559078378417)
                ·
                  refine ⟨25131088778569919308783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33508118371426559078378417 25131088778569919308783813)
                  ·
                    refine ⟨4712079145981859870396965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25131088778569919308783813 4712079145981859870396965)
                    ·
                      refine ⟨883514839871598725699431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4712079145981859870396965 883514839871598725699431)
                      ·
                        rfl

theorem cell23_1720639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1720639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720639 prefixEnd_1720639 := by exact prefixLift 1720639
  have htrace : WordTrace (prefixWord ++ tailWord_1720639) baseStart_1720639 baseEnd_1720639 := by
    simpa [prefixWord, tailWord_1720639, baseEnd_1720639] using wordTrace_append hprefix tailTrace_1720639
  have hstable : (prefixWord ++ tailWord_1720639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720639).length < 2 ^ (prefixWord ++ tailWord_1720639).sum := by decide
  have hdescent : baseEnd_1720639 < baseStart_1720639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720727 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 1, 1, 3]
def baseStart_1720727 : Nat := 118140960795 + 1720727 * 2 ^ 59
def prefixEnd_1720727 : Nat := 4983230072969 + 3 ^ 40 * 1720727 * 2
def baseEnd_1720727 : Nat := 883560026169194381399027

theorem tailTrace_1720727 : CollatzResearch.WordTrace tailWord_1720727 prefixEnd_1720727 883560026169194381399027 := by
  unfold tailWord_1720727
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760069637107430619984435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41840046424738287079989623 62760069637107430619984435)
  ·
    refine ⟨94140104455661145929976653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62760069637107430619984435 94140104455661145929976653)
    ·
      refine ⟨35302539170872929723741245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94140104455661145929976653 35302539170872929723741245)
      ·
        refine ⟨13238452189077348646402967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35302539170872929723741245 13238452189077348646402967)
        ·
          refine ⟨19857678283616022969604451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238452189077348646402967 19857678283616022969604451)
          ·
            refine ⟨29786517425424034454406677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19857678283616022969604451 29786517425424034454406677)
            ·
              refine ⟨1396243004316751615050313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29786517425424034454406677 1396243004316751615050313)
              ·
                refine ⟨1047182253237563711287735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396243004316751615050313 1047182253237563711287735)
                ·
                  refine ⟨1570773379856345566931603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047182253237563711287735 1570773379856345566931603)
                  ·
                    refine ⟨2356160069784518350397405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570773379856345566931603 2356160069784518350397405)
                    ·
                      refine ⟨883560026169194381399027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2356160069784518350397405 883560026169194381399027)
                      ·
                        rfl

theorem cell23_1720727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_1720727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720727 prefixEnd_1720727 := by exact prefixLift 1720727
  have htrace : WordTrace (prefixWord ++ tailWord_1720727) baseStart_1720727 baseEnd_1720727 := by
    simpa [prefixWord, tailWord_1720727, baseEnd_1720727] using wordTrace_append hprefix tailTrace_1720727
  have hstable : (prefixWord ++ tailWord_1720727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720727).length < 2 ^ (prefixWord ++ tailWord_1720727).sum := by decide
  have hdescent : baseEnd_1720727 < baseStart_1720727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
